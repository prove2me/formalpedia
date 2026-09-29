-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isSectionBasisOn_pullback_comp_iff_of_toProj_comp_eq
-- name    : AlgebraicGeometry.Scheme.Modules.isSectionBasisOn_pullback_comp_iff_of_toProj_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/9ce32764-9264-5b90-83a4-f6f12d80c136
-- title:
--   Basis condition transfers along compatible P^N-presentations
-- statement:
--   Let $S \to S'$ be a ring homomorphism (given as an $S$-algebra structure on $S'$), let $N$ be a natural number, let $Z, Z'$ be schemes with structure morphisms $f : Z \to \operatorname{Spec} S$ and $f' : Z' \to \operatorname{Spec} S'$, and let $L$, $L'$ be modules on $Z$, $Z'$ respectively. Suppose $\mathfrak{P}$ is a `ProjPresentation` of $L$ over $f$ of degree $N$ and $\mathfrak{P}'$ one of $L'$ over $f'$: each consists of global sections $\sigma_0,\dots,\sigma_N$ of the module, a morphism `toProj` to $\operatorname{Proj}$ of the homogeneous subalgebra of the polynomial ring in $N+1$ variables over the base ring whose composite with the projection $\pi$ is the structure morphism, the condition that over any open contained in the preimage of the basic open $D(X_i)$ multiplication by $\sigma_i$ is a bijection from functions to sections, and the condition that over the preimage of $D(X_i)$ the pullback of the ratio $X_j/X_i$ times $\sigma_i$ equals $\sigma_j$. Let $e : Z' \to Z$ satisfy $\mathfrak{P}.\mathrm{toProj} \circ e = \mathrm{ProjSpace.map}\,S\,S'\,N \circ \mathfrak{P}'.\mathrm{toProj}$. Then for every scheme $A$ with a morphism $f'' : A \to \operatorname{Spec} S''$ over a ring $S''$ and every $g : A \to Z'$, the following are equivalent: the map $(c_i) \mapsto \sum_i f''^{\sharp}(c_i)\cdot \mathrm{pullbackLocalSection}(g \circ e)(\sigma_i)$ is a bijection from $S''^{\,N+1}$ onto the sections of $(g \circ e)^{*}L$ over $(g\circ e)^{-1}(\top)$; and the corresponding map built from $\mathrm{pullbackLocalSection}(g)(\sigma'_i)$ is a bijection onto the sections of $g^{*}L'$ over $g^{-1}(\top)$. Here $\mathrm{pullbackLocalSection}$ denotes the unit of the pullback–pushforward adjunction applied to a section.
--
--   This is the statement that the condition 'the coordinate sections pull back to an $S''$-basis of global sections' depends only on the morphism to projective space, not on the chosen presentation, and is compatible with base change $\mathbb{P}^N_{S'} \to \mathbb{P}^N_S$. It is used in the construction of an immersion of a framed polarised abelian scheme into projective space over a Noetherian base, where the basis condition is checked after pulling back along a test morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isSectionBasisOn_pullback_comp_iff_of_toProj_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.isSectionBasisOn_pullback_comp_iff_of_toProj_comp_eq
    {S S' : Type} [CommRing S] [CommRing S'] [Algebra S S'] {N : ℕ}
    {Z Z' : Scheme.{0}} {f : Z ⟶ Spec (CommRingCat.of S)} {f' : Z' ⟶ Spec (CommRingCat.of S')}
    {L : Z.Modules} {L' : Z'.Modules}
    (𝔓 : Scheme.Modules.ProjPresentation L f N) (𝔓' : Scheme.Modules.ProjPresentation L' f' N)
    (e : Z' ⟶ Z) (heι : e ≫ 𝔓.toProj = 𝔓'.toProj ≫ ProjSpace.map S S' N)
    {S'' : Type} [CommRing S''] {A : Scheme.{0}} (f'' : A ⟶ Spec (CommRingCat.of S'')) (g : A ⟶ Z') :
    Scheme.Modules.IsSectionBasisOn f'' ((Scheme.Modules.pullback (g ≫ e)).obj L) ((g ≫ e) ⁻¹ᵁ ⊤)
        (fun i => Scheme.Modules.pullbackLocalSection (g ≫ e) (𝔓.σ i)) ↔
      Scheme.Modules.IsSectionBasisOn f'' ((Scheme.Modules.pullback g).obj L') (g ⁻¹ᵁ ⊤)
        (fun i => Scheme.Modules.pullbackLocalSection g (𝔓'.σ i)) := by sorry
