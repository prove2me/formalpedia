-- Prove2me | Theorems.Thm_AlgebraicGeometry_stalkMap_germ_app_appIso_inv_appTop_eq_germ_appTop_of_comp_spec_map_eq_isoOfEq_hom_comp_morphismRestrict_comp
-- name    : AlgebraicGeometry.stalkMap_germ_app_appIso_inv_appTop_eq_germ_appTop_of_comp_spec_map_eq_isoOfEq_hom_comp_morphismRestrict_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/0ef31de0-140f-57c7-ad5f-049af2a20e1b
-- title:
--   Germs agree after base change of a Spec-chart
-- statement:
--   Let $\mathrm{pr} : X' \to X$ be a morphism of schemes, $U$ an open subset of $X$, and $Q, Q'$ commutative rings. Let $f$ be a morphism from the open subscheme $U$ to $\operatorname{Spec} Q$. Write $W := \mathrm{pr}^{-1}(\iota_U(\top))$ for the preimage under $\mathrm{pr}$ of the open image of the whole of $U$ under the open immersion $\iota_U : U \to X$, and assume $hWU$: $W = \mathrm{pr}^{-1}(U)$ as opens of $X'$, with $(X'.\mathrm{isoOfEq}\ hWU)$ the resulting isomorphism of open subschemes. Let $g$ be a morphism from the open subscheme $W$ to $\operatorname{Spec} Q'$, let $\psi : Q \to Q'$ be a ring homomorphism, and assume the square commutes in the form $g$ followed by $\operatorname{Spec}(\psi)$ equals $(X'.\mathrm{isoOfEq}\ hWU)$ followed by the restriction $\mathrm{pr} \mid_U$ followed by $f$. Let $t \in Q$, let $x' \in X'$ and let $hx'$ witness $x' \in W$. Starting from $t$, transport it to a global section of $\operatorname{Spec} Q$ by the inverse of $\Gamma\operatorname{Spec}$, pull it back along $f$ to a section over the whole of the open subscheme $U$, identify this with a section of $X$ over $\iota_U(\top)$ by the inverse of the open-immersion isomorphism $\iota_U.\mathrm{appIso}\ \top$, pull back along $\mathrm{pr}$ to a section of $X'$ over $W$, and take its germ at $x'$; applying the stalk map of the open immersion $\iota_W$ at $\langle x', hx'\rangle$ gives an element of the stalk of $W$ at that point. The assertion is that this element equals the germ at $\langle x', hx'\rangle$ of the section of $W$ over its whole space obtained by transporting $\psi(t)$ to a global section of $\operatorname{Spec} Q'$ and pulling it back along $g$.
--
--   This is the functoriality bookkeeping for germs along a commuting square of charts: the pullback of a coordinate $t$ through the chart $f$ on $U$ and the pullback of its image $\psi(t)$ through the chart $g$ on the preimage define the same element of the stalk at a point of the preimage. It is used in the construction of base-changed étale charts for the model of the modular curve at $p$, where $t$ runs over the crossing coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_stalkMap_germ_app_appIso_inv_appTop_eq_germ_appTop_of_comp_spec_map_eq_isoOfEq_hom_comp_morphismRestrict_comp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.stalkMap_germ_app_appIso_inv_appTop_eq_germ_appTop_of_comp_spec_map_eq_isoOfEq_hom_comp_morphismRestrict_comp
    {X X' : Scheme.{u}} (pr : X' ⟶ X) (U : X.Opens) {Q Q' : Type u} [CommRing Q] [CommRing Q']
    (f : (↑U : Scheme.{u}) ⟶ Spec (CommRingCat.of Q))
    (hWU : pr ⁻¹ᵁ (U.ι ''ᵁ ⊤) = pr ⁻¹ᵁ U)
    (g : (↑(pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)) : Scheme.{u}) ⟶ Spec (CommRingCat.of Q')) (ψ : Q →+* Q')
    (hfac : g ≫ Spec.map (CommRingCat.ofHom ψ) = (X'.isoOfEq hWU).hom ≫ (pr ∣_ U) ≫ f)
    (t : Q) (x' : ↥X') (hx' : x' ∈ pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)) :
    ((pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)).ι.stalkMap ⟨x', hx'⟩).hom
        ((X'.presheaf.germ (pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)) x' hx').hom
          ((pr.app (U.ι ''ᵁ ⊤)).hom ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom t))))) =
      ((↑(pr ⁻¹ᵁ (U.ι ''ᵁ ⊤)) : Scheme.{u}).presheaf.germ ⊤ ⟨x', hx'⟩ trivial).hom
        ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of Q')).inv.hom (ψ t))) := by sorry
