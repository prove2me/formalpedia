-- Prove2me | Theorems.Thm_AlgebraicGeometry_isAffineOpen_preimage_fst_and_exists_eq_sum_of_isAffineOpen
-- name    : AlgebraicGeometry.isAffineOpen_preimage_fst_and_exists_eq_sum_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/ebca90ed-6aac-5400-a508-ef92b4b6c82b
-- title:
--   Affineness of pr₁⁻¹V and generation of its sections by Γ(V) and C
-- statement:
--   Let $\mathcal{O}$ and $C$ be commutative rings (in the lowest universe), $\varphi : \mathcal{O} \to C$ a ring homomorphism, $\mathcal{X}$ a scheme and $f : \mathcal{X} \to \operatorname{Spec}\mathcal{O}$ a morphism, and let $s_C : \operatorname{Spec} C \to \operatorname{Spec}\mathcal{O}$ be a morphism assumed to be equal to $\operatorname{Spec}$ of $\varphi$. Let $V$ be an open subscheme of $\mathcal{X}$ which is an affine open. Write $\mathrm{pr}_1 =$ `Limits.pullback.fst f sC` and $\mathrm{pr}_2 =$ `Limits.pullback.snd f sC` for the two projections from the fibre product $\mathcal{X} \times_{\operatorname{Spec}\mathcal{O}} \operatorname{Spec} C$. The assertion is twofold: first, the open $\mathrm{pr}_1^{-1}V$ of the fibre product is again an affine open; second, for every section $t \in \Gamma(\mathrm{pr}_1^{-1}V, \mathcal{O}_{\mathcal{X}\times \operatorname{Spec} C})$ there are a natural number $m$, sections $a_0,\dots,a_{m-1} \in \Gamma(V, \mathcal{O}_{\mathcal{X}})$ and elements $c_0,\dots,c_{m-1} \in C$ with $t = \sum_{i<m} \bigl(\mathrm{pr}_2^{\sharp}(c_i)\bigr)\big|_{\mathrm{pr}_1^{-1}V} \cdot \mathrm{pr}_1^{\sharp}(a_i)$, where $\mathrm{pr}_2^{\sharp}(c_i)$ denotes the image of $c_i$ under the inverse of the canonical isomorphism $\Gamma(\operatorname{Spec} C) \cong C$ followed by the map on global sections induced by $\mathrm{pr}_2$, restricted from the whole space to $\mathrm{pr}_1^{-1}V$, and $\mathrm{pr}_1^{\sharp}$ is the map $\Gamma(V,\mathcal{O}_{\mathcal{X}}) \to \Gamma(\mathrm{pr}_1^{-1}V, \mathcal{O})$ induced by $\mathrm{pr}_1$.
--
--   This is the standard affine base-change statement $\Gamma(\mathrm{pr}_1^{-1}V) \cong \Gamma(V) \otimes_{\mathcal{O}} C$, recorded in the weaker form of affineness of $\mathrm{pr}_1^{-1}V$ together with surjectivity of the multiplication map, so that users need not name the isomorphism. It is used in the work on the Čerednik–Drinfeld uniformisation, in the construction of covers on which prescribed sections of a quotient are expressed in terms of sections over an affine open and scalars from $C$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isAffineOpen_preimage_fst_and_exists_eq_sum_of_isAffineOpen.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isAffineOpen_preimage_fst_and_exists_eq_sum_of_isAffineOpen
    {𝒪 C : Type} [CommRing 𝒪] [CommRing C] (φ : 𝒪 →+* C)
    {𝒳 : Scheme.{0}} (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
    (sC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of 𝒪)) (hsC : sC = Spec.map (CommRingCat.ofHom φ))
    (V : 𝒳.Opens) (hV : IsAffineOpen V) :
    IsAffineOpen ((Limits.pullback.fst f sC) ⁻¹ᵁ V) ∧
    ∀ t : (Limits.pullback f sC).presheaf.obj (Opposite.op ((Limits.pullback.fst f sC) ⁻¹ᵁ V)),
      ∃ (m : ℕ) (a : Fin m → 𝒳.presheaf.obj (Opposite.op V)) (c : Fin m → C),
        t = ∑ i, ((Limits.pullback f sC).presheaf.map (homOfLE (le_top : (Limits.pullback.fst f sC) ⁻¹ᵁ V ≤ ⊤)).op).hom
              ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c i))) *
            ((Limits.pullback.fst f sC).app V).hom (a i) := by sorry
