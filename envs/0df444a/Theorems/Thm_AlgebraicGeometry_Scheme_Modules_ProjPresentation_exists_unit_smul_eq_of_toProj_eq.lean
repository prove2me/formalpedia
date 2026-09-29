-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_unit_smul_eq_of_toProj_eq
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_unit_smul_eq_of_toProj_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/0d25a47c-7cae-5a53-b04d-86dbca250a32
-- title:
--   Proj presentations of a fixed morphism differ by a global unit
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $M$ an $\mathcal O_X$-module, $f : X \to \operatorname{Spec} R$ a morphism and $N$ a natural number. A `ProjPresentation` of $M$ along $f$ of rank $N$ consists of global sections $\sigma_0,\dots,\sigma_N \in \Gamma(M,\top)$ together with a morphism $\varphi : X \to \operatorname{Proj}$ of the homogeneous coordinate ring $R[x_0,\dots,x_N]$ (that is, $\mathbb P^N_R$) such that: $\varphi$ followed by the structure morphism `ProjSpace.π` is $f$; for every index $i$ and every open $V \subseteq X$ contained in $\varphi^{-1}D_+(x_i)$, the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot (\sigma_i|_V)$, is bijective, so $\sigma_i$ frames $M$ there; and for all $i,j$ the pullback under $\varphi$ of the degree-zero section $x_j/x_i$ on $D_+(x_i)$ multiplied by $\sigma_i|_{\varphi^{-1}D_+(x_i)}$ equals $\sigma_j|_{\varphi^{-1}D_+(x_i)}$. Given two such presentations $P$ and $P'$ whose morphisms to $\mathbb P^N_R$ coincide, the theorem produces a unit $u \in \Gamma(X,\top)^{\times}$ of the ring of global sections of $\mathcal O_X$ with $P'.\sigma_i = u \cdot P.\sigma_i$ for every $i \in \{0,\dots,N\}$.
--
--   This is the uniqueness half of the classical correspondence between morphisms to $\mathbb P^N$ and systems of generating sections of an invertible module: the framing sections are determined by the morphism up to a single global unit. It is used in the treatment of framed polarised abelian schemes, in particular for the comparison of reframings and for the projective embedding and pullback statements about them, and it underlies the variant `exists_unit_appTop_smul_eq_of_toProj_eq_of_bijective`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_unit_smul_eq_of_toProj_eq.lean

import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_unit_smul_eq_of_toProj_eq
    {R : Type u} [CommRing R] {X : Scheme.{u}} {M : X.Modules} {f : X ⟶ Spec (.of R)} {N : ℕ}
    (P P' : M.ProjPresentation f N) (h : P.toProj = P'.toProj) :
    ∃ u : (Γ(X, ⊤))ˣ, ∀ i : Fin (N + 1), P'.σ i = (u : Γ(X, ⊤)) • P.σ i := by sorry
