-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_isClosedImmersion_one_and_forall_iff_isInStabilizer_of_kernelTrivial
-- name    : AlgebraicGeometry.Polarisation.isClosedImmersion_one_and_forall_iff_isInStabilizer_of_kernelTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/1ee241b3-ee70-507d-bf3b-d8685254ce8e
-- title:
--   Kernel trivial: unit section represents the stabiliser
-- statement:
--   Let $K$ be a field, $A$ a scheme (in universe $0$) and $f : A \to \operatorname{Spec} K$ a morphism, equipped with a `RelativeGroupLaw` $L$ over $K$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ of $A$-points over each $t : T \to \operatorname{Spec} K$, with multiplication, unit and inverse natural in $T$. Assume the bundle `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal L$ be a module over $A$ which is invertible (locally on $A$ its restriction is isomorphic to the unit module), and assume `KernelTrivial f L 𝓛`: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} K$ and every $A$-point $x$ over $t$, if the pullback along `sliceAt f x` of the Mumford bundle $m^*\mathcal L \otimes p_1^*\mathcal L^\vee \otimes p_2^*\mathcal L^\vee$ on $A \times_{\operatorname{Spec} K} A$ is, locally over points of $\operatorname{Spec} R$, isomorphic to the unit module on $A \times_{\operatorname{Spec} K} \operatorname{Spec} R$, then $x$ is the unit point over $t$. Write $e$ for the underlying morphism $\operatorname{Spec} K \to A$ of the unit point over $\mathrm{id}_{\operatorname{Spec} K}$. The conclusion is fourfold: $e$ is a closed immersion; $e$ followed by $f$ is finite; the finrank of $e$ followed by $f$ at the closed point of $\operatorname{Spec} K$ equals $1$; and for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} K$ and every $A$-point $x$ over $t$, there exists $x_0 : \operatorname{Spec} R \to \operatorname{Spec} K$ with $x_0$ followed by $e$ equal to $x$ if and only if `L.IsInStabilizer 𝓛 t x`, i.e. the pullback of $\mathcal L$ along translation by $x$ is, locally over points of $\operatorname{Spec} R$, isomorphic to the pullback of $\mathcal L$ along the first projection $A \times_{\operatorname{Spec} K} \operatorname{Spec} R \to A$.
--
--   This is the statement that, when the theta group kernel $K(\mathcal L)$ of an invertible sheaf on an abelian scheme over a field is scheme-theoretically trivial, the unit section is a closed subscheme of $A$, finite of rank one over the base, and represents the stabiliser functor of $\mathcal L$. It supplies the hypothesis block used in deducing $\chi(\mathcal L)^2 = 1$ for a principal polarisation, and is invoked in the study of fake elliptic curves arising from quaternionic modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_isClosedImmersion_one_and_forall_iff_isInStabilizer_of_kernelTrivial.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.isClosedImmersion_one_and_forall_iff_isInStabilizer_of_kernelTrivial
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (hA : AbelianSchemePropertyBundle K f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hK : KernelTrivial f L 𝓛) :
    IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of K)))).1 ∧
      IsFinite ((L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f) ∧
      ((L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f).finrank (IsLocalRing.closedPoint K) = 1 ∧
      ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
        (∃ x₀ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K), x₀ ≫ (L.one (𝟙 (Spec (CommRingCat.of K)))).1 = x.1) ↔
          L.IsInStabilizer 𝓛 t x := by sorry
