-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_tensor_pullback_negMor_iso_of_comp_eq
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_tensor_pullback_negMor_iso_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/e23d6099-c36b-5e6a-91a1-61c6da9664e5
-- title:
--   Transport of M ⊗ [-1]^*M along a base-change transition map
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, and let $L$ be a relative group law for $f$ over $S$: an operation assigning to each scheme $T$ and each $t : T \to \operatorname{Spec} S$ a multiplication, unit and inverse on the set of $\varphi : T \to A$ with $\varphi$ followed by $f$ equal to $t$, satisfying associativity, the two unit laws, the left inverse law, and compatibility of the multiplication with precomposition by morphisms $T' \to T$ over $\operatorname{Spec} S$. Let $T_1, T_2$ be commutative rings and $s_1 : S \to T_1$, $s_2 : S \to T_2$, $\tau : T_1 \to T_2$ ring homomorphisms with $\tau \circ s_1 = s_2$. Write $A_i := A \times_{\operatorname{Spec} S} \operatorname{Spec} T_i$ for the pullback of $f$ along $\operatorname{Spec}$ of $s_i$, and let $[-1]_i$ denote the endomorphism of $A_i$ obtained as the underlying morphism of the $L$-inverse, for the base-changed law `RelativeGroupLaw.baseChange` on the second projection $A_i \to \operatorname{Spec} T_i$, of the identity point of $A_i$ over itself. Let $\rho : A_2 \to A_1$ satisfy $\rho$ followed by the first projection equals the first projection of $A_2$, and $\rho$ followed by the second projection equals the second projection of $A_2$ followed by $\operatorname{Spec}\tau$. Then for every module $\mathcal M$ on $A_1$ the type of isomorphisms $\rho^*(\mathcal M \otimes [-1]_1^*\mathcal M) \cong \rho^*\mathcal M \otimes [-1]_2^*(\rho^*\mathcal M)$ is nonempty.
--
--   This is the compatibility of the symmetry construction $\mathcal M \mapsto \mathcal M \otimes [-1]^*\mathcal M$ with a change of base ring, for the transition morphism between two base changes of a scheme carrying a relative group law. It is used in the treatment of symmetric line bundles and principal square roots on base-changed abelian schemes, in particular by the results on symmetry of polarisations after base change and on geometric fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_tensor_pullback_negMor_iso_of_comp_eq.lean

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

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_tensor_pullback_negMor_iso_of_comp_eq
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {T₁ T₂ : Type} [CommRing T₁] [CommRing T₂] (s₁ : S →+* T₁) (s₂ : S →+* T₂) (τ : T₁ →+* T₂)
    (hτ : τ.comp s₁ = s₂)
    (ρ : pullback f (Spec.map (CommRingCat.ofHom s₂)) ⟶ pullback f (Spec.map (CommRingCat.ofHom s₁)))
    (hρ₁ : ρ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom s₁)) = pullback.fst f (Spec.map (CommRingCat.ofHom s₂)))
    (hρ₂ : ρ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom s₁)) =
      pullback.snd f (Spec.map (CommRingCat.ofHom s₂)) ≫ Spec.map (CommRingCat.ofHom τ))
    (𝓜 : (pullback f (Spec.map (CommRingCat.ofHom s₁))).Modules) :
    Nonempty ((Scheme.Modules.pullback ρ).obj
        (𝓜 ⊗ (Scheme.Modules.pullback
          (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom s₁))) (L.baseChange (Spec.map (CommRingCat.ofHom s₁))))).obj 𝓜) ≅
      (Scheme.Modules.pullback ρ).obj 𝓜 ⊗ (Scheme.Modules.pullback
        (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom s₂))) (L.baseChange (Spec.map (CommRingCat.ofHom s₂))))).obj
          ((Scheme.Modules.pullback ρ).obj 𝓜)) := by sorry
