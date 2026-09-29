-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_app_unit_and_toProj_eq_comp_of_iso
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_sigma_eq_app_unit_and_toProj_eq_comp_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/061e2f13-be5c-542f-a646-df54ab27aedd
-- title:
--   Transport of a Proj presentation along an isomorphism
-- statement:
--   Let $S$ be a commutative ring, $N$ a natural number, and let $e : A \cong A'$ be an isomorphism of schemes equipped with morphisms $f : A \to \operatorname{Spec} S$ and $f' : A' \to \operatorname{Spec} S$ satisfying $f = f' \circ e$ (in diagrammatic form `e.hom ≫ f' = f`). Let $M$ be a sheaf of modules on $A$, $M'$ one on $A'$, and $\psi$ an isomorphism from the pullback of $M'$ along `e.hom` to $M$. Let $P'$ be a `ProjPresentation` of $M'$ over $f'$ of size $N$, that is: global sections $\sigma'_0,\dots,\sigma'_N \in \Gamma(M',\top)$ together with a morphism `P'.toProj` from $A'$ to $\operatorname{Proj}$ of the homogeneous coordinate algebra $S[X_0,\dots,X_N]$ whose composite with the structure map to $\operatorname{Spec} S$ is $f'$, such that on every open $V$ contained in the preimage of the basic open $D(X_i)$ multiplication $g \mapsto g \cdot \sigma'_i|_V$ is a bijection $\Gamma(A',V) \to \Gamma(M',V)$, and such that on the preimage of $D(X_i)$ the pullback of the ratio $X_j/X_i$ times $\sigma'_i$ equals $\sigma'_j$. Assume further that `P'.toProj` is a closed immersion and that $P'.\sigma$ is a section basis for $f'$, i.e. the map $(c_i) \mapsto \sum_i f'^{\sharp}(c_i)\cdot\sigma'_i$ from $S^{N+1}$ to $\Gamma(M',\top)$ is bijective. Then there exists a `ProjPresentation` $P$ of $M$ over $f$ of the same size $N$ with $\sigma_i = \psi(\text{unit}_{M'}(\sigma'_i))$ on global sections, where the unit is that of the pullback–pushforward adjunction along `e.hom`, with `P.toProj` equal to `e.hom` followed by `P'.toProj`, with `P.toProj` a closed immersion, and with $P.\sigma$ a section basis for $f$.
--
--   This is the transport of a presentation of a module by $N+1$ global sections framing it over the standard charts of $\mathbb{P}^N_S$ along an isomorphism of the base schemes and a compatible isomorphism of modules, together with the preservation of the two extra properties (closed immersion, and the sections forming a free $S$-basis of the global sections). It is used in the construction of coverings by reframed objects for framed polarised abelian schemes, where a frame on one object must be carried onto an isomorphic one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_app_unit_and_toProj_eq_comp_of_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_sigma_eq_app_unit_and_toProj_eq_comp_of_iso
    {S : Type u} [CommRing S] {N : ℕ} {A A' : Scheme.{u}} (e : A ≅ A')
    {f : A ⟶ Spec (.of S)} {f' : A' ⟶ Spec (.of S)} (he : e.hom ≫ f' = f)
    {M : A.Modules} {M' : A'.Modules} (ψ : (Scheme.Modules.pullback e.hom).obj M' ≅ M)
    (P' : M'.ProjPresentation f' N) (h₁ : IsClosedImmersion P'.toProj)
    (h₂ : Scheme.Modules.IsSectionBasis f' M' P'.σ) :
    ∃ P : M.ProjPresentation f N,
      (∀ i : Fin (N + 1), P.σ i =
        ψ.hom.app ⊤ ((((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app M').app ⊤) (P'.σ i))) ∧
      P.toProj = e.hom ≫ P'.toProj ∧ IsClosedImmersion P.toProj ∧ Scheme.Modules.IsSectionBasis f M P.σ := by sorry
