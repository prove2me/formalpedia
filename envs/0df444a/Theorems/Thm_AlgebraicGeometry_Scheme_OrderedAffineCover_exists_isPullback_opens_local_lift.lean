-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_isPullback_opens_local_lift
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.exists_isPullback_opens_local_lift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/17425576-e0a9-556d-92cc-30b8456a0cb0
-- title:
--   Restriction of a local smooth lift to an open subscheme
-- statement:
--   Let $T'$ and $T$ be commutative rings and $\pi : T' \to T$ a surjective ring homomorphism whose kernel ideal is nilpotent. Let $A_0$ be a scheme and $f_0 : A_0 \to \operatorname{Spec} T$ a separated morphism, and let $\mathcal{U}$ be an ordered affine cover of $A_0$, that is: a finite linearly ordered index type $\iota$ together with opens $U_a \subseteq A_0$, each affine, whose supremum is $\top$. Suppose given for each $a \in \iota$ a scheme $Y_a$, a smooth morphism $q_a : Y_a \to \operatorname{Spec} T'$ and a morphism $g_a : U_a \to Y_a$ making the square with sides $g_a$, the inclusion $U_a \hookrightarrow A_0$ followed by $f_0$, $q_a$ and $\operatorname{Spec}(\pi)$ cartesian. Suppose further given, for each $a$, an assignment $O_a$ from opens of $A_0$ to opens of $Y_a$ such that $g_a^{-1}(O_a(W))$ equals the preimage of $W$ under $U_a \hookrightarrow A_0$ for every open $W$, such that $O_a$ is monotone, $O_a(U_a) = \top$, $O_a(W) \cap O_a(W') \le O_a(W \cap W')$, and $O_a(W)$ is affine whenever $W$ is an affine open contained in $U_a$. Then for any index $a$ and any affine open $W \le U_a$: the composite $O_a(W) \hookrightarrow Y_a \xrightarrow{q_a} \operatorname{Spec} T'$ is smooth, and there exists $\gamma : W \to O_a(W)$ with $\gamma$ followed by $O_a(W) \hookrightarrow Y_a$ equal to the inclusion $W \hookrightarrow U_a$ followed by $g_a$, such that the square with sides $\gamma$, $W \hookrightarrow A_0$ followed by $f_0$, the above composite $O_a(W) \to \operatorname{Spec} T'$, and $\operatorname{Spec}(\pi)$ is cartesian.
--
--   This is the localisation step in the deformation-theoretic gluing of smooth lifts along a nilpotent thickening $\operatorname{Spec} T \hookrightarrow \operatorname{Spec} T'$: the piece of a chartwise lift cut out over an open $W$ of the chart is again a smooth lift of $W$. It feeds into [`AlgebraicGeometry.Smooth.exists_overlap_isos_local_lifts`](thm.html#AlgebraicGeometry.Smooth.exists_overlap_isos_local_lifts), where lifts over two charts are compared on their overlap.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_isPullback_opens_local_lift.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_isPullback_opens_local_lift
    (T' T : Type u) [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀]
    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W'))
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W))
    (a : 𝒰.ι) (W : A₀.Opens) (hWaff : IsAffineOpen W) (hW : W ≤ 𝒰.U a) :
    Smooth ((O a W).ι ≫ q a) ∧
    ∃ γ : (↑W : Scheme.{u}) ⟶ ↑(O a W),
      γ ≫ (O a W).ι = A₀.homOfLE hW ≫ g a ∧
      IsPullback γ (W.ι ≫ f₀) ((O a W).ι ≫ q a) (Spec.map (CommRingCat.ofHom π)) := by sorry
