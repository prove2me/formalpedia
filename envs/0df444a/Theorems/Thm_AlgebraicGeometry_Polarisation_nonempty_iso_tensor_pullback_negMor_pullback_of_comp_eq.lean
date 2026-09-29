-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_iso_tensor_pullback_negMor_pullback_of_comp_eq
-- name    : AlgebraicGeometry.Polarisation.nonempty_iso_tensor_pullback_negMor_pullback_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/58b5748c-e3a1-5a87-855b-e357ff6a3699
-- title:
--   Transport of a square root mathcal L₀ along a base-change transition map
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$, equipped with a relative group law $L$ on $f$, that is, functorial multiplication, unit and inversion operations on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} S$, satisfying associativity, the two unit laws, left inversion, and naturality of multiplication under change of $T$. Let $T_1, T_2$ be commutative rings and $s_1 : S \to T_1$, $s_2 : S \to T_2$, $\tau : T_1 \to T_2$ ring homomorphisms with $\tau \circ s_1 = s_2$, and write $A_{T_i}$ for the pullback of $f$ along $\operatorname{Spec}(s_i)$, with projections $p_i$ to $A$ and $\pi_i$ to $\operatorname{Spec} T_i$. Let $\rho : A_{T_2} \to A_{T_1}$ be a morphism with $\rho$ followed by $p_1$ equal to $p_2$, and $\rho$ followed by $\pi_1$ equal to $\pi_2$ followed by $\operatorname{Spec}(\tau)$. Let $\mathcal L$ be an $\mathcal O_A$-module and $\mathcal L_0$ an $\mathcal O_{A_{T_1}}$-module. Write $[-1]_i$ for `negMor` of the base-changed group law $L$ on $\pi_i$, i.e. the underlying morphism $A_{T_i} \to A_{T_i}$ obtained by applying that law's inversion operation to the identity point of $A_{T_i}$ over $\pi_i$. Assuming an isomorphism $p_1^*\mathcal L \cong \mathcal L_0 \otimes [-1]_1^*\mathcal L_0$ exists, the conclusion is that an isomorphism $p_2^*\mathcal L \cong \rho^*\mathcal L_0 \otimes [-1]_2^*(\rho^*\mathcal L_0)$ exists. Both hypothesis and conclusion assert mere non-emptiness of the relevant sets of isomorphisms of modules, not a chosen one.
--
--   This is the transport step for square roots of a line bundle along the group law: a solution $\mathcal L_0$ of $p^*\mathcal L \cong \mathcal L_0 \otimes [-1]^*\mathcal L_0$ over one base change is carried by pullback to any further base change compatible with it. It is used in passing such a root along a chain of base changes down to a geometric fibre, and is cited by [`AlgebraicGeometry.Polarisation.exists_isInvertible_nonempty_iso_tensor_pullback_negMor_geomFibre_of_field`](thm.html#AlgebraicGeometry.Polarisation.exists_isInvertible_nonempty_iso_tensor_pullback_negMor_geomFibre_of_field).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_iso_tensor_pullback_negMor_pullback_of_comp_eq.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_iso_tensor_pullback_negMor_pullback_of_comp_eq
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {T₁ T₂ : Type} [CommRing T₁] [CommRing T₂] (s₁ : S →+* T₁) (s₂ : S →+* T₂) (τ : T₁ →+* T₂)
    (hτ : τ.comp s₁ = s₂)
    (ρ : pullback f (Spec.map (CommRingCat.ofHom s₂)) ⟶ pullback f (Spec.map (CommRingCat.ofHom s₁)))
    (hρ₁ : ρ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom s₁)) = pullback.fst f (Spec.map (CommRingCat.ofHom s₂)))
    (hρ₂ : ρ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom s₁)) =
      pullback.snd f (Spec.map (CommRingCat.ofHom s₂)) ≫ Spec.map (CommRingCat.ofHom τ))
    (𝓛 : A.Modules) (𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom s₁))).Modules)
    (e : Nonempty ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom s₁)))).obj 𝓛 ≅
      𝓛₀ ⊗ (Scheme.Modules.pullback
        (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom s₁))) (L.baseChange (Spec.map (CommRingCat.ofHom s₁))))).obj 𝓛₀)) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom s₂)))).obj 𝓛 ≅
      (Scheme.Modules.pullback ρ).obj 𝓛₀ ⊗ (Scheme.Modules.pullback
        (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom s₂))) (L.baseChange (Spec.map (CommRingCat.ofHom s₂))))).obj
          ((Scheme.Modules.pullback ρ).obj 𝓛₀)) := by sorry
