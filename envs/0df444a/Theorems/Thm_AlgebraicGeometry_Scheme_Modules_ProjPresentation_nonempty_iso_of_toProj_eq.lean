-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_nonempty_iso_of_toProj_eq
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.nonempty_iso_of_toProj_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/2262bad5-7204-5514-82d7-c3776d9b9507
-- title:
--   Uniqueness of a module presenting a map to P^N_R
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} R$ a morphism, $M$ and $M'$ two $\mathcal O_X$-modules (objects of `X.Modules`), and $N$ a natural number. Suppose given data $\mathfrak P$ presenting $M$ and $\mathfrak Q$ presenting $M'$ over $f$ with $N+1$ coordinates; such data consist of global sections $\sigma_0,\dots,\sigma_N \in \Gamma(M,\top)$, a morphism $\mathrm{toProj} : X \to \operatorname{Proj}$ of the graded ring of homogeneous components of $R[x_0,\dots,x_N]$ whose composite with the structure map $\pi$ to $\operatorname{Spec} R$ is $f$, the requirement that for every $i$ and every open $V \le \mathrm{toProj}^{-1}D_+(x_i)$ the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g\cdot(\sigma_i|_V)$, is bijective, and the requirement that for all $i,j$ the pullback along $\mathrm{toProj}$ of the degree-zero fraction $x_j/x_i$ on $D_+(x_i)$ multiplies $\sigma_i$ into $\sigma_j$ after restriction to $\mathrm{toProj}^{-1}D_+(x_i)$. If the two presentations have the same associated morphism, $\mathfrak P.\mathrm{toProj} = \mathfrak Q.\mathrm{toProj}$, then the type of isomorphisms $M \cong M'$ in `X.Modules` is nonempty. Only the existence of an isomorphism is asserted; no compatibility with the sections is recorded in the conclusion.
--
--   This is the uniqueness half of the classical description of morphisms to projective space by an invertible sheaf together with generating sections: the line bundle (here, the module framed by the $\sigma_i$ on the charts) is determined up to isomorphism by the morphism it presents. It is used in the framed rigidity results for polarised abelian schemes, for instance in the construction of immersions into projective space and in the comparison of realisations of such presentations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_nonempty_iso_of_toProj_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.nonempty_iso_of_toProj_eq
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M M' : X.Modules} {N : ℕ}
    (𝔓 : M.ProjPresentation f N) (𝔔 : M'.ProjPresentation f N) (h : 𝔓.toProj = 𝔔.toProj) :
    Nonempty (M ≅ M') := by sorry
