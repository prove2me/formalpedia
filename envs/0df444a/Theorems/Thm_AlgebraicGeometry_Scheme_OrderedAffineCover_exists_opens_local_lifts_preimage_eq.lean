-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_opens_local_lifts_preimage_eq
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.exists_opens_local_lifts_preimage_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/8878493e-d88a-5ca9-b13b-3332c27d6de2
-- title:
--   Opens of a local lift above the opens of the base
-- statement:
--   Let $T'$ be a local ring, $T$ a ring, and $\pi \colon T' \to T$ a surjective ring homomorphism whose kernel is nilpotent, satisfies $\ker\pi \cdot \mathfrak m_{T'} = 0$, and is contained in $\mathfrak m_{T'}$. Let $f_0 \colon A_0 \to \operatorname{Spec} T$ be a morphism of schemes and let $\mathcal U$ be an `OrderedAffineCover` of $A_0$, i.e. a finite linearly ordered index type $\iota$ together with opens $U_a \subseteq A_0$, each affine, whose supremum is $\top$. Suppose given for each $a \in \iota$ a scheme $Y_a$, a smooth morphism $q_a \colon Y_a \to \operatorname{Spec} T'$, and a morphism $g_a \colon U_a \to Y_a$ (source the open subscheme $U_a$) such that the square formed by $g_a$, the composite of the inclusion $U_a \hookrightarrow A_0$ with $f_0$, $q_a$ and $\operatorname{Spec}\pi$ is cartesian. The conclusion asserts the existence of maps $O_a$ from the opens of $A_0$ to the opens of $Y_a$ such that: $g_a^{-1}(O_a(W))$ equals the preimage of $W$ under the inclusion $U_a \hookrightarrow A_0$; each $O_a$ is monotone; $O_a(U_a) = \top$; $O_a(W) \sqcap O_a(W') \le O_a(W \sqcap W')$; and $O_a(W)$ is an affine open whenever $W$ is an affine open with $W \le U_a$.
--
--   This provides, for each chart of the cover, a compatible system of opens of the smooth lift $Y_a$ lying over the opens of the base, with affineness preserved on affine opens contained in the chart; it is the device that transports affine Čech data from $A_0$ to the lifts. It is used in the construction of the two-cocycle in point derivations measuring the obstruction to gluing local lifts over a small extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_opens_local_lifts_preimage_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct
  AlgebraicGeometry.SmallExtension Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_opens_local_lifts_preimage_eq
    (T' T : Type u) [CommRing T'] [IsLocalRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥) (hI : RingHom.ker π ≤ maximalIdeal T')
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T))
    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π))) :
    ∃ (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W')),
      ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W) := by sorry
