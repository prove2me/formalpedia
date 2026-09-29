-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_sigma_eq_smul
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_sigma_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/77d29d13-dc6f-5a6e-8179-c498734a9441
-- title:
--   Unit-proportional sections give the same morphism to P^N
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $M$ a module over $X$, $f : X \to \operatorname{Spec} R$ a morphism, and $N$ a natural number. Let $P$ and $P'$ be two terms of type `M.ProjPresentation f N`; such a term consists of global sections $\sigma_i \in \Gamma(M, \top)$ indexed by $i \in \mathrm{Fin}(N+1)$, a morphism `toProj` from $X$ to $\operatorname{Proj}$ of the graded ring of homogeneous components of $R[x_0,\dots,x_N]$, subject to: `toProj` followed by the structure morphism `ProjSpace.π R N` equals $f$; for each $i$ and each open $V \le \mathrm{toProj}^{-1}D_+(x_i)$, the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot (\sigma_i|_V)$, is bijective; and for all $i,j$, the pullback along `toProj` of the section of $D_+(x_i)$ determined by the degree-zero fraction $x_j/x_i$ (i.e. `ProjSpace.ratio R N i j` viewed via `Proj.awayToSection`) acts on $\sigma_i$ restricted to $\mathrm{toProj}^{-1}D_+(x_i)$ to give $\sigma_j$ restricted to the same open. Assume $c \in \Gamma(X, \top)$ is a unit and $P'.\sigma\, i = c \cdot P.\sigma\, i$ for every $i \in \mathrm{Fin}(N+1)$. Then $P'.\mathrm{toProj} = P.\mathrm{toProj}$.
--
--   This is the uniqueness half of the classical description of morphisms to projective space by a line-bundle-like module together with $N+1$ generating sections: proportional systems of sections, the factor being a global unit, induce the same morphism to $\mathbb P^N_R$. It is used in the construction of isomorphisms and pullback squares for framed polarised abelian schemes, notably by [`AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_mk_of_iso_of_forall_sigma_eq_smul`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_mk_of_iso_of_forall_sigma_eq_smul), [`AlgebraicGeometry.FramedPolarisedAbelianScheme.isPullback_of_isPullback_of_isReframe`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.isPullback_of_isPullback_of_isReframe) and [`AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_isReframe_inter_one`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_isReframe_inter_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_sigma_eq_smul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_sigma_eq_smul
    {R : Type u} [CommRing R] {X : Scheme.{u}} {M : X.Modules} {f : X ⟶ Spec (CommRingCat.of R)} {N : ℕ}
    (P P' : M.ProjPresentation f N) (c : Γ(X, ⊤)) (hc : IsUnit c)
    (h : ∀ i : Fin (N + 1), P'.σ i = c • P.σ i) :
    P'.toProj = P.toProj := by sorry
