-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_kernelTrivial_of_isIso_of_forall_iff_isInStabilizer
-- name    : AlgebraicGeometry.Polarisation.kernelTrivial_of_isIso_of_forall_iff_isInStabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/ddf56c52-925a-5298-a53d-65e72e2f9241
-- title:
--   Stabiliser represented by the base gives trivial kernel
-- statement:
--   Let $K$ be a field, let $A$ and $Z$ be schemes, let $f : A \to \operatorname{Spec} K$ be a morphism, and let $L$ be a relative group law on $f$, i.e. a functorial group structure (multiplication, unit, inverse, with associativity, unit and inverse laws, and naturality of multiplication under base change) on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over $t : T \to \operatorname{Spec} K$. Let $\mathcal L$ be a module on $A$ that is invertible, in the sense that every point of $A$ has an open neighbourhood on which the restriction of $\mathcal L$ is isomorphic to the unit module. Let $\iota : Z \to A$ be a closed immersion such that $\iota$ followed by $f$ is an isomorphism, and assume that $\iota$ represents the stabiliser of $\mathcal L$: for every scheme $T$, every $t : T \to \operatorname{Spec} K$ and every $T$-point $x$ of $A$ over $t$, the morphism $x$ factors through $\iota$ if and only if `L.IsInStabilizer 𝓛 t x` holds, that is, the pullback of $\mathcal L$ along the right translation $\operatorname{mulRight}$ by $x$ on $A \times_{\operatorname{Spec} K} T$ and the pullback of $\mathcal L$ along the first projection become isomorphic after restriction over some open neighbourhood in $T$ of each point of $T$. The conclusion is `KernelTrivial f L 𝓛`: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} K$ and every $T$-point $x$ of $A$ over $t$, if the pullback along $\operatorname{sliceAt} f\,x$ of the Mumford bundle $m^*\mathcal L \otimes (p_1^*\mathcal L^\vee \otimes p_2^*\mathcal L^\vee)$ on $A \times_{\operatorname{Spec} K} A$ is, locally over each point of $\operatorname{Spec} R$, isomorphic to the unit module on $A \times_{\operatorname{Spec} K} \operatorname{Spec} R$, then $x$ is the unit point $L.\mathrm{one}\,t$.
--
--   This is the scheme-theoretic statement that the kernel $K(\mathcal L)$ of the polarisation attached to $\mathcal L$, described via local triviality of slices of the Mumford bundle, is trivial once the stabiliser functor of $\mathcal L$ is represented by a closed subscheme isomorphic to the base. It is the final step in deducing $K(\mathcal L) = e$ from the computation of the order of the kernel, and is used in the derivation of kernel triviality from the Euler-characteristic condition $\chi(\mathcal L)^2 = 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_kernelTrivial_of_isIso_of_forall_iff_isInStabilizer.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.kernelTrivial_of_isIso_of_forall_iff_isInStabilizer
    (K : Type) [Field K] {A Z : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (ι : Z ⟶ A) [IsClosedImmersion ι] [IsIso (ι ≫ f)]
    (hZ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ κ : T ⟶ Z, κ ≫ ι = x.1) ↔ L.IsInStabilizer 𝓛 t x) :
    KernelTrivial f L 𝓛 := by sorry
