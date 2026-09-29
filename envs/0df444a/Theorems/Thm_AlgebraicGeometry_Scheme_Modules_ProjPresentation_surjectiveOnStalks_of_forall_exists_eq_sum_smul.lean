-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_surjectiveOnStalks_of_forall_exists_eq_sum_smul
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.surjectiveOnStalks_of_forall_exists_eq_sum_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/e770450d-1fa4-565f-96d3-112ac9f8c588
-- title:
--   Surjectivity on stalks transfers along R-linear spans of presentations
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} R$ a morphism, $M$ a module over $X$, and $N, N'$ natural numbers. Let $\mathfrak{P}$ be a `ProjPresentation` of $M$ over $f$ of size $N$ and $\mathfrak{Q}$ one of size $N'$; such a datum consists of global sections $\sigma_i \in \Gamma(M, \top)$ indexed by $i \in \mathrm{Fin}(N+1)$, a morphism $\mathfrak{P}.\mathrm{toProj} : X \to \operatorname{Proj}$ of the homogeneous coordinate ring $R[X_0,\dots,X_N]$ whose composite with the structure morphism $\mathbb{P}^N_R \to \operatorname{Spec} R$ is $f$, the requirement that over every open $V \subseteq X$ lying in the preimage of the basic open $D_+(X_i)$ the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot \sigma_i|_V$, be bijective, and the requirement that over the preimage of $D_+(X_i)$ the pullback of the degree-zero element $X_j/X_i$ multiplied by $\sigma_i$ equal $\sigma_j$. Assume $\mathfrak{P}.\mathrm{toProj}$ is surjective on stalks, and that for every $i$ there are coefficients $c_j \in R$ with $\mathfrak{P}.\sigma_i = \sum_j (f^\sharp(c_j)) \cdot \mathfrak{Q}.\sigma_j$, the scalars being the images of the $c_j$ in $\Gamma(X,\top)$ under the global sections map of $f$. Then $\mathfrak{Q}.\mathrm{toProj}$ is surjective on stalks.
--
--   This is the comparison step in the theory of morphisms to projective space attached to a system of generating sections: if the sections framing one presentation lie in the $R$-span of those of a second, then the second morphism inherits surjectivity on stalks. It feeds into [`AlgebraicGeometry.Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_forall_exists_eq_sum_smul`](thm.html#AlgebraicGeometry.Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_forall_exists_eq_sum_smul), where surjectivity on stalks is one half of the closed-immersion criterion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_surjectiveOnStalks_of_forall_exists_eq_sum_smul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.surjectiveOnStalks_of_forall_exists_eq_sum_smul
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N N' : ℕ}
    (𝔓 : M.ProjPresentation f N) (𝔔 : M.ProjPresentation f N') [SurjectiveOnStalks 𝔓.toProj]
    (h : ∀ i : Fin (N + 1), ∃ c : Fin (N' + 1) → R,
      𝔓.σ i = ∑ j, (f.appTop ((Scheme.ΓSpecIso (.of R)).inv (c j))) • 𝔔.σ j) :
    SurjectiveOnStalks 𝔔.toProj := by sorry
