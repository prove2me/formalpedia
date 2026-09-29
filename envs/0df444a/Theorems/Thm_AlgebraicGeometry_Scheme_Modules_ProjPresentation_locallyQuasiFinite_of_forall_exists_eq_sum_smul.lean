-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_locallyQuasiFinite_of_forall_exists_eq_sum_smul
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.locallyQuasiFinite_of_forall_exists_eq_sum_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/68f6b732-4bf1-580e-b265-4fe339d3770a
-- title:
--   Locally quasi-finiteness transfers along R-linear combinations of sections
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $f\colon X\to\operatorname{Spec} R$ a morphism, $M$ an $\mathcal O_X$-module, and $N,N'$ natural numbers. Let $\mathfrak P$ and $\mathfrak Q$ be projective presentations of $M$ over $f$ of sizes $N$ and $N'$: thus $\mathfrak P$ consists of global sections $\sigma_i\in\Gamma(M,\top)$ for $i\in\{0,\dots,N\}$ together with a morphism $\mathfrak P.\mathrm{toProj}\colon X\to\operatorname{Proj}$ of the graded ring of homogeneous polynomials in $N+1$ variables over $R$, such that composing it with the structure morphism `ProjSpace.π` recovers $f$, such that for every $i$ and every open $V\subseteq X$ contained in the preimage of the basic open $D_+(X_i)$ the map $\Gamma(X,V)\to\Gamma(M,V)$, $g\mapsto g\cdot(\sigma_i|_V)$, is bijective, and such that for all $i,j$ the pullback along $\mathfrak P.\mathrm{toProj}$ of the section $X_j/X_i$ of the away-localisation at $X_i$ acts on $\sigma_i$, restricted to the preimage of $D_+(X_i)$, to give $\sigma_j$ restricted there; similarly for $\mathfrak Q$ with $N'+1$ sections. Assume $\mathfrak P.\mathrm{toProj}$ is locally quasi-finite, and that each $\sigma_i$ equals $\sum_j c_j\cdot\mathfrak Q.\sigma_j$ for some $c\colon\{0,\dots,N'\}\to R$, the coefficients acting through $R\cong\Gamma(\operatorname{Spec} R,\top)\to\Gamma(X,\top)$. Then $\mathfrak Q.\mathrm{toProj}$ is locally quasi-finite.
--
--   This is a comparison statement for two presentations of the same module by global sections defining morphisms to projective spaces: if the generating sections of one presentation are $R$-linear combinations of those of the other, local quasi-finiteness of the associated morphism to projective space passes from the latter to the former. It is used in the construction of away-local finiteness by sections for modules, notably by [`AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_forall_mem_finset_away`](thm.html#AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_forall_mem_finset_away) and [`AlgebraicGeometry.Scheme.Modules.exists_away_finiteBySections_tensorPow_of_forall_geometricFibre`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_away_finiteBySections_tensorPow_of_forall_geometricFibre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_locallyQuasiFinite_of_forall_exists_eq_sum_smul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.locallyQuasiFinite_of_forall_exists_eq_sum_smul
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N N' : ℕ}
    (𝔓 : M.ProjPresentation f N) (𝔔 : M.ProjPresentation f N') [LocallyQuasiFinite 𝔓.toProj]
    (h : ∀ i : Fin (N + 1), ∃ c : Fin (N' + 1) → R,
      𝔓.σ i = ∑ j, (f.appTop ((Scheme.ΓSpecIso (.of R)).inv (c j))) • 𝔔.σ j) :
    LocallyQuasiFinite 𝔔.toProj := by sorry
