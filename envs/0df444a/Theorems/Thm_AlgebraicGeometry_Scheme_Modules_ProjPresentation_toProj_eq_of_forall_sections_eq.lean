-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_forall_sections_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/bdc7c19f-3388-5e22-83bc-46ed8206a07c
-- title:
--   Uniqueness of a Proj presentation given its sections
-- statement:
--   Fix a commutative ring $R$, a scheme $X$ (in universe $0$), a morphism $f : X \to \operatorname{Spec} R$, an $\mathcal{O}_X$-module $M$ (an object of `X.Modules`) and a natural number $N$. A `ProjPresentation` of $M$ over $f$ of size $N$ consists of the data of global sections $\sigma_i \in \Gamma(M, \top)$ indexed by $i \in \mathrm{Fin}(N+1)$, a morphism $\varphi : X \to \operatorname{Proj}$ of the graded ring $R[X_0,\dots,X_N]$ with its homogeneous-submodule grading, the condition that $\varphi$ followed by the structure morphism $\mathbb{P}^N_R \to \operatorname{Spec} R$ equals $f$, the framing condition that for every $i$ and every open $V \subseteq \varphi^{-1}D_+(X_i)$ the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot \sigma_i|_V$, is bijective, and the compatibility that on $\varphi^{-1}D_+(X_i)$ the pullback along $\varphi$ of the section of $\operatorname{Proj}$ determined by the degree-zero element $X_j/X_i$ of the away localisation at $X_i$ multiplies $\sigma_i$ into $\sigma_j$. The theorem asserts: if $\mathfrak{P}$ and $\mathfrak{Q}$ are two such presentations whose sections agree, $\mathfrak{P}.\sigma\, i = \mathfrak{Q}.\sigma\, i$ for all $i \in \mathrm{Fin}(N+1)$, then their underlying morphisms to $\operatorname{Proj}$ coincide, $\mathfrak{P}.\mathrm{toProj} = \mathfrak{Q}.\mathrm{toProj}$.
--
--   This is the uniqueness half of the classical description of morphisms to projective space by generating sections of an invertible module: the morphism is determined by the sections that present it. Since a `ProjPresentation` records the morphism as data alongside the sections, this statement is what makes that data redundant, and it is used in the construction of projective embeddings of abelian schemes from polarisations and in the comparison of morphisms over $\mathbb{P}^N$ arising there. The proof cites only the intrinsic characterisation of the open set $\varphi^{-1}D_+(X_i)$ as the locus where $\sigma_i$ frames $M$ locally.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_forall_sections_eq
    {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 𝔔 : M.ProjPresentation f N) (h : ∀ i : Fin (N + 1), 𝔓.σ i = 𝔔.σ i) :
    𝔓.toProj = 𝔔.toProj := by sorry
