-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_pullback_of_isFinite
-- name    : AlgebraicGeometry.Scheme.Modules.FiniteBySections.pullback_of_isFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/7ac7bbfe-4153-5dc7-89a5-d1cff4dff22d
-- title:
--   Finite-by-sections is preserved by pull-back along a finite morphism
-- statement:
--   Let $R$ be a commutative ring, let $X, X'$ be schemes, let $f : X \to \operatorname{Spec} R$ be a morphism, let $p : X' \to X$ be a finite morphism, and let $M$ be an $\mathcal O_X$-module (an object of `X.Modules`). Assume `Scheme.Modules.FiniteBySections M f`, i.e. there are $N \in \mathbb{N}$ and a `ProjPresentation` of $M$ over $f$ of size $N$ whose associated morphism to $\operatorname{Proj}$ is finite; such a presentation consists of global sections $\sigma_i \in \Gamma(M, \top)$ for $i \in \mathrm{Fin}(N+1)$, a morphism $\mathrm{toProj} : X \to \operatorname{Proj}$ of the homogeneous submodule of $R[X_0,\dots,X_N]$ (projective $N$-space over $R$) whose composite with the projection $\pi$ to $\operatorname{Spec} R$ is $f$, the requirement that for every $i$ and every open $V \le \mathrm{toProj}^{-1}(D(X_i))$ the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot \sigma_i|_V$, is bijective, and the compatibility that on $\mathrm{toProj}^{-1}(D(X_i))$ the pulled-back ratio section $X_j/X_i$ times $\sigma_i$ equals $\sigma_j$. The conclusion is that the pull-back $(\mathrm{pullback}\, p).obj\, M$ is finite by sections over the composite $p$ followed by $f$.
--
--   The statement records that the project's notion of an $\mathcal O_X$-module being finite by sections over $\operatorname{Spec} R$ — presented by $N+1$ global sections framing a finite morphism to $\mathbb P^N_R$ — is stable under pull-back along a finite morphism, with the base $\operatorname{Spec} R$ unchanged. It is used in the construction of polarisations and in the treatment of fake elliptic curves, where pulling a line bundle back along a finite endomorphism must preserve finiteness by sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_pullback_of_isFinite.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.FiniteBySections.pullback_of_isFinite
    {R : Type u} [CommRing R] {X X' : Scheme.{u}} {f : X ⟶ Spec (.of R)} (p : X' ⟶ X) [IsFinite p]
    {M : X.Modules} (hM : Scheme.Modules.FiniteBySections M f) :
    Scheme.Modules.FiniteBySections ((Scheme.Modules.pullback p).obj M) (p ≫ f) := by sorry
