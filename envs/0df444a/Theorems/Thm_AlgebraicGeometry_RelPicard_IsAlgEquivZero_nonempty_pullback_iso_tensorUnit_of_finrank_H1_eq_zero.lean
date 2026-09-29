-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_pullback_iso_tensorUnit_of_finrank_H1_eq_zero
-- name    : AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_pullback_iso_tensorUnit_of_finrank_H1_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/43cbb3b7-4098-58a8-861c-04031807bc75
-- title:
--   Algebraically trivial line bundles pull back trivially to genus-zero curves
-- statement:
--   Let $k$ be an algebraically closed field, let $X$ be a scheme with a morphism $x\colon X\to\operatorname{Spec} k$, and let $L$ be a sheaf of modules on $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ such that the pullback of $L$ along the inclusion $U\hookrightarrow X$ is isomorphic to the unit module of $U$. Assume `IsAlgEquivZero x L`: there are a scheme $T'$ with a locally of finite type, geometrically integral morphism $h\colon T'\to\operatorname{Spec} k$, an invertible module $M$ on $X\times_{\operatorname{Spec} k}T'$, and two sections $t_0,t_1$ of $h$ over $\operatorname{Spec} k$, such that the pullback of $M$ along the base change of $t_0$ is isomorphic to the unit module of $X\times_{\operatorname{Spec} k}\operatorname{Spec} k$ and the pullback of $M$ along the base change of $t_1$ is isomorphic to the pullback of $L$ along the first projection. Let further $y\colon Y\to\operatorname{Spec} k$ with $Y$ integral, $y$ proper and smooth of relative dimension $1$, and let $\mathcal{W}$ be a two-chart affine cover of $Y$, i.e. affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\cap U_1$ affine. Assume that the $k$-dimension of the first Čech cohomology of $\mathcal{W}$ with coefficients in the structure sheaf — the quotient of $\Gamma(\mathcal{O}_Y,U_0\cap U_1)$ by the image of the difference of the two restriction maps from $\Gamma(\mathcal{O}_Y,U_0)\times\Gamma(\mathcal{O}_Y,U_1)$ — is zero. Then for every morphism $i\colon Y\to X$ with $i$ followed by $x$ equal to $y$, the pullback $i^{*}L$ is isomorphic to the unit object of the monoidal category of $Y$-modules.
--
--   This is the statement that a line bundle algebraically equivalent to zero restricts to the trivial bundle along any map from a proper smooth integral curve of genus zero (genus being measured by the vanishing of $h^1$ of the structure sheaf on a two-chart cover). It is used in the analysis of relative Picard functors of curve models, in particular by the results on triviality of algebraically trivial bundles pulled back to the rational-function curve model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_pullback_iso_tensorUnit_of_finrank_H1_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_pullback_iso_tensorUnit_of_finrank_H1_eq_zero
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero x L)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    [IsIntegral Y] [IsProper y] [SmoothOfRelativeDimension 1 y]
    (𝒲 : Y.TwoAffineOpenCover)
    (h10 : Module.finrank k (𝒲.sectionsOf y (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)).H1 = 0)
    (i : Y ⟶ X) (hi : i ≫ x = y) :
    Nonempty ((Scheme.Modules.pullback i).obj L ≅ 𝟙_ Y.Modules) := by sorry
