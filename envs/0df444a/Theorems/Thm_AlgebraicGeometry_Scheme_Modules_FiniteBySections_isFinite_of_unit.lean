-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit
-- name    : AlgebraicGeometry.Scheme.Modules.FiniteBySections.isFinite_of_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/926ec842-cae7-524f-88d5-67e1461c15ab
-- title:
--   Finiteness of f from a finite presentation of 𝒪_X
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme and $f\colon X\to\operatorname{Spec} R$ a morphism of schemes. Assume the project's condition `Scheme.Modules.FiniteBySections` holds for the structure sheaf of $X$, viewed as the unit object `SheafOfModules.unit X.ringCatSheaf` of the category of $\mathcal{O}_X$-modules, relative to $f$; by definition this means that there are an $N\in\mathbb{N}$ and a `ProjPresentation` of this module over $f$ of size $N$ whose structural morphism `toProj` is a finite morphism. Such a presentation consists of: global sections $\sigma_0,\dots,\sigma_N\in\Gamma(X,\mathcal{O}_X)$; a morphism $\varphi\colon X\to\operatorname{Proj}$ of the graded ring of polynomials in $N+1$ variables over $R$ (that is, $\mathbb{P}^N_R$) with $\varphi$ followed by the projection `ProjSpace.π` equal to $f$; the condition that for every $i$ and every open $V\subseteq\varphi^{-1}D_+(x_i)$ the map $g\mapsto g\cdot(\sigma_i|_V)$ from $\Gamma(X,V)$ to the sections of the module over $V$ is bijective; and the condition that on $\varphi^{-1}D_+(x_i)$ the pullback along $\varphi$ of the ratio $x_j/x_i$ multiplied by $\sigma_i$ equals $\sigma_j$. The conclusion is that $f$ is a finite morphism, `IsFinite f`.
--
--   This is the step which converts a projective presentation of the structure sheaf with finite associated morphism to $\mathbb{P}^N_R$ into finiteness of $X$ over $\operatorname{Spec} R$, the scheme-theoretic content being that a quasi-affine proper morphism is finite. It is used by [`AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_finiteBySections_unit`](thm.html#AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_finiteBySections_unit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.FiniteBySections.isFinite_of_unit
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (h𝒪 : Scheme.Modules.FiniteBySections (SheafOfModules.unit X.ringCatSheaf : X.Modules) f) :
    IsFinite f := by sorry
