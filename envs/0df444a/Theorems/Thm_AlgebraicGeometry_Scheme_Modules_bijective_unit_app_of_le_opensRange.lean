-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
-- name    : AlgebraicGeometry.Scheme.Modules.bijective_unit_app_of_le_opensRange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/437fb08a-96e3-574e-8f35-1eadc18056c8
-- title:
--   Unit of pullback adjunction is bijective on sections inside the image
-- statement:
--   Let $j\colon Y \to X$ be a morphism of schemes (in a fixed universe) which is an open immersion, let $N$ be an object of `X.Modules`, i.e. a sheaf of $\mathcal O_X$-modules, and let $V$ be an open subset of $X$ contained in the open range `j.opensRange` of $j$, that is, $V \le j(Y)$. The adjunction `Scheme.Modules.pullbackPushforwardAdjunction j` has inverse image along $j$ as left adjoint and direct image along $j$ as right adjoint; its unit evaluated at $N$ is a morphism of sheaves of $\mathcal O_X$-modules $N \to j_* j^* N$. The assertion is that the component of this morphism at the open set $V$, namely the map on sections
--   $$\Gamma(V, N) \longrightarrow \Gamma(j^{-1}V, j^*N),$$
--   is bijective as a function between the underlying modules. Note that bijectivity is asserted only for opens $V$ inside the image of $j$, and only at the level of sections over a single open, not as an isomorphism of sheaves.
--
--   This is the standard fact that for an open immersion the inverse image of a sheaf of modules is its restriction, so that sections over an open inside the image are unchanged by pulling back. It is used throughout the treatment of line bundles and sections on abelian schemes and relative Picard groups, where sections over an open of the base are identified with sections of a pullback, for instance in the construction of framings and of theta points, and in the exactness statements for pushforwards of ideal sheaves of sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange.lean

import Mathlib.AlgebraicGeometry.Modules.Sheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.bijective_unit_app_of_le_opensRange
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (N : X.Modules)
    (V : X.Opens) (hV : V ≤ j.opensRange) :
    Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).app V) := by sorry
