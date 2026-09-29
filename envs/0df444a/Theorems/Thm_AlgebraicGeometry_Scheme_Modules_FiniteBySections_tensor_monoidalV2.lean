-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.FiniteBySections.tensor_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/2e442045-fb71-50bf-ba6b-6569f92acfad
-- title:
--   Tensor product preserves finiteness by sections
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme and $f\colon X\to\operatorname{Spec} R$ a morphism, and let $L$ and $M$ be sheaves of modules on $X$ (objects of `X.Modules`). Assume both $L$ and $M$ are finite by sections over $f$, that is: for each of them there is an $N\in\mathbb N$ together with a projective presentation of degree $N$ over $f$ whose structure morphism is a finite morphism. Here a projective presentation of a module $M$ consists of global sections $\sigma_0,\dots,\sigma_N\in\Gamma(M,\top)$ and a morphism $\mathrm{toProj}\colon X\to\operatorname{Proj}$ of the graded ring of homogeneous polynomials in $N+1$ variables over $R$ (i.e. $\mathbb P^N_R$) such that $\mathrm{toProj}$ followed by the structure map $\mathbb P^N_R\to\operatorname{Spec} R$ equals $f$; such that for every $i$ and every open $V\subseteq X$ contained in the preimage under $\mathrm{toProj}$ of the basic open set $D_+(X_i)$ the map $\Gamma(X,V)\to\Gamma(M,V)$, $g\mapsto g\cdot(\sigma_i|_V)$, is bijective; and such that for all $i,j$ the pullback along $\mathrm{toProj}$ of the section of the $X_i$-away algebra given by the ratio $X_j/X_i$ acts on $\sigma_i$, restricted to the preimage of $D_+(X_i)$, to give $\sigma_j$ restricted there. The conclusion is that the tensor product $L\otimes M$ in `X.Modules` is again finite by sections over $f$.
--
--   This is the multiplicativity of the property of being finite by sections: passing from presentations of $L$ and $M$ of degrees $N$ and $N'$ to a presentation of $L\otimes M$ of degree $NN'+N+N'$ realised through the Segre embedding $\mathbb P^N_R\times_R\mathbb P^{N'}_R\hookrightarrow\mathbb P^{NN'+N+N'}_R$, the sections $\sigma_i\otimes\tau_j$ serving as the new presenting sections. It is used in the construction of fake elliptic curves for the Čerednik–Drinfeld theory, both to produce Rosati-compatible modules that are finite by sections over an algebraically closed base and to build towers of finite morphisms to projective spaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor_monoidalV2.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.Scheme.Modules.FiniteBySections.tensor_monoidalV2
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
    {L M : X.Modules} (hL : L.FiniteBySections f) (hM : M.FiniteBySections f) :
    (L ⊗ M).FiniteBySections f := by sorry
