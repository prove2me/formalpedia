-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_sum_smul_toProj_eq_comp_linMap
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_sigma_eq_sum_smul_toProj_eq_comp_linMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/efcd32be-6a12-540e-adb8-b366b3854a96
-- title:
--   Reframing a projective presentation by an invertible matrix
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} R$ a morphism, $M$ a sheaf of $\mathcal O_X$-modules on $X$, and $N$ a natural number. Let $\mathfrak P$ be a projective presentation of $M$ over $f$ of size $N$, that is: global sections $\sigma_i \in \Gamma(M,\top)$ for $i \in \{0,\dots,N\}$ together with a morphism $\mathfrak P.\mathrm{toProj} : X \to \operatorname{Proj}$ of the graded ring of homogeneous components of $R[x_0,\dots,x_N]$, such that $\mathfrak P.\mathrm{toProj}$ followed by the structure morphism $\mathrm{ProjSpace}.\pi$ equals $f$; such that for every $i$ and every open $V \subseteq X$ contained in the preimage of the basic open $D_+(x_i)$, multiplication by a section of $\mathcal O_X$ on $V$ against the restriction of $\sigma_i$ to $V$ is a bijection $\Gamma(X,V) \to \Gamma(M,V)$ (i.e. $\sigma_i$ is a frame there); and such that for all $i,j$ the pullback along $\mathfrak P.\mathrm{toProj}$ of the section of $D_+(x_i)$ determined by the degree-zero element $x_j/x_i$ of the localisation away from $x_i$, acting on the restriction of $\sigma_i$ to the preimage of $D_+(x_i)$, equals the restriction of $\sigma_j$ there. Let $U$ be an $(N+1)\times(N+1)$ matrix over $R$ and $hU$ a proof that $U$ is a unit of the matrix ring. The conclusion asserts the existence of a projective presentation $\mathfrak P'$ of the same $M$ over the same $f$, of the same size $N$, whose sections are $\mathfrak P'.\sigma_i = \sum_j \bar U_{ij} \cdot \mathfrak P.\sigma_j$, where $\bar U_{ij} \in \Gamma(X,\top)$ is the image of $U_{ij}$ under the inverse of the isomorphism $R \cong \Gamma(\operatorname{Spec} R,\top)$ followed by the map on global sections induced by $f$, and whose morphism to projective space is $\mathfrak P.\mathrm{toProj}$ followed by the projective linear automorphism $\mathrm{ProjSpace.linMap}\,R\,N\,U\,hU$, i.e. $\operatorname{Proj}$ of the graded substitution $x_i \mapsto \sum_j U_{ij}x_j$.
--
--   This is the functoriality of the morphism to projective space under an invertible linear change of the generating sections: replacing the frame $(\sigma_i)$ by $(\sum_j U_{ij}\sigma_j)$ post-composes the classifying morphism with the corresponding projective linear automorphism of $\mathbb P^N_R$. It provides the existence half of the reframing operation on projective presentations, the converse direction (recovering the morphism from the transformed sections) being recorded in [`AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_comp_linMap_of_sigma_eq_sum_smul`](thm.html#AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_comp_linMap_of_sigma_eq_sum_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_sum_smul_toProj_eq_comp_linMap.lean

import Definitions.Def_AlgebraicGeometry_ProjSpaceLinMap
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_sigma_eq_sum_smul_toProj_eq_comp_linMap
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 : M.ProjPresentation f N) (U : Matrix (Fin (N + 1)) (Fin (N + 1)) R) (hU : IsUnit U) :
    ∃ 𝔓' : M.ProjPresentation f N,
      (∀ i, 𝔓'.σ i = ∑ j, ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of R)).inv.hom (U i j))) • 𝔓.σ j) ∧
      𝔓'.toProj = 𝔓.toProj ≫ ProjSpace.linMap R N U hU := by sorry
