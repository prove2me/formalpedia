-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_finiteBySections_unit
-- name    : AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_finiteBySections_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/b23e4da9-9eb4-5a3d-8bd5-081bf6d31458
-- title:
--   Invertible modules are finite by sections when mathcal O_X is
-- statement:
--   Let $R$ be a commutative ring and let $f \colon X \to \operatorname{Spec} R$ be a proper morphism of schemes. Assume that the unit module $\mathcal O_X$, viewed as a sheaf of modules on $X$, is finite by sections over $f$: there are an $N$ and a projective presentation of $\mathcal O_X$ of size $N$, i.e. global sections $\sigma_0,\dots,\sigma_N \in \Gamma(X,\mathcal O_X)$ together with a morphism $\varphi \colon X \to \operatorname{Proj}$ of the homogeneous coordinate algebra on $N+1$ variables over $R$ such that $\varphi$ followed by the structural projection to $\operatorname{Spec} R$ is $f$, such that for every open $V \subseteq \varphi^{-1}D_+(x_i)$ multiplication by the restriction of $\sigma_i$ is a bijection of $\Gamma(X,V)$ onto $\Gamma(\mathcal O_X,V)$, and such that on $\varphi^{-1}D_+(x_i)$ the pullback of the ratio $x_j/x_i$ carries $\sigma_i$ to $\sigma_j$, with $\varphi$ in addition a finite morphism. Let $M$ be a sheaf of modules on $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ for which the pullback of $M$ along $U \hookrightarrow X$ is isomorphic to the unit module of $U$. Then $M$ is finite by sections over $f$ as well: some finite family of global sections of $M$ gives a projective presentation of $M$ whose associated morphism to a projective space over $R$ is finite.
--
--   This is the step saying that the property 'finite by sections' spreads from the structure sheaf to all line bundles on a proper $R$-scheme, the hypothesis on $\mathcal O_X$ forcing $X$ itself to be finite over $\operatorname{Spec} R$. It feeds the construction of opens over which tensor powers of a module become finite by sections, used in the analysis of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_finiteBySections_unit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_finiteBySections_unit
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (h𝒪 : Scheme.Modules.FiniteBySections (SheafOfModules.unit X.ringCatSheaf : X.Modules) f)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Scheme.Modules.FiniteBySections M f := by sorry
