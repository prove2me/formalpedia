-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_iso_forall_app_eq_of_toProj_eq
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_iso_forall_app_eq_of_toProj_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/e33e5683-762f-5060-aeab-11008f5dccf9
-- title:
--   Projective presentations with equal XtoP^N are framed-isomorphic
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} R$ a morphism, $M$ and $M'$ two $\mathcal{O}_X$-modules (objects of `X.Modules`), and $N$ a natural number. Suppose given data $P$ and $Q$ of type `ProjPresentation` for $M$ and $M'$ respectively, relative to $f$ and $N$: each consists of a family of global sections indexed by $\mathrm{Fin}(N+1)$ (written $\sigma_i \in \Gamma(M,\top)$, resp. $\Gamma(M',\top)$), a morphism `toProj` from $X$ to $\operatorname{Proj}$ of the graded ring $R[x_0,\dots,x_N]$ (the homogeneous submodules of `MvPolynomial (Fin (N+1)) R`) whose composite with the structure morphism `ProjSpace.π R N` is $f$, the framing condition that for every $i$ and every open $V \subseteq X$ contained in the preimage under `toProj` of the basic open $D_+(x_i)$ the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot (\sigma_i|_V)$, is bijective, and the compatibility that for all $i,j$ the pullback along `toProj` of the section of $\operatorname{Proj}$ on $D_+(x_i)$ determined by $x_j/x_i$ acts on $\sigma_i$, restricted to `toProj ⁻¹ᵁ` $D_+(x_i)$, to give $\sigma_j$ there. Assume the two morphisms to $\operatorname{Proj}$ coincide: $P.\mathrm{toProj} = Q.\mathrm{toProj}$. Then there is an isomorphism $\varphi : M \cong M'$ of $\mathcal{O}_X$-modules such that for every $i \in \mathrm{Fin}(N+1)$ the map $\varphi$ on global sections sends $P.\sigma_i$ to $Q.\sigma_i$.
--
--   This is the rigidity half of the classical correspondence between morphisms $X \to \mathbb{P}^N_R$ over $R$ and data consisting of an invertible sheaf with $N+1$ generating sections: the module together with its presenting sections is determined, up to an isomorphism matching the sections, by the induced morphism to projective space. It is used in the treatment of framed polarised abelian schemes, for instance in [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_thetaPt_act_eq_iff_exists_translate_comp_toProj_eq`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_thetaPt_act_eq_iff_exists_translate_comp_toProj_eq), [`AlgebraicGeometry.FramedPolarisedAbelianScheme.isThetaAdapted_of_iso`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.isThetaAdapted_of_iso) and [`AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_iso_of_isReframe`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_iso_of_isReframe).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_iso_forall_app_eq_of_toProj_eq.lean

import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_iso_forall_app_eq_of_toProj_eq
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M M' : X.Modules} {N : ℕ}
    (P : M.ProjPresentation f N) (Q : M'.ProjPresentation f N) (h : P.toProj = Q.toProj) :
    ∃ φ : M ≅ M', ∀ i : Fin (N + 1), φ.hom.app ⊤ (P.σ i) = Q.σ i := by sorry
