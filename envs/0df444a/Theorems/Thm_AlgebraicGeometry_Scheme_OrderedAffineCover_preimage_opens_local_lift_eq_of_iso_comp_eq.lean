-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_preimage_opens_local_lift_eq_of_iso_comp_eq
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_opens_local_lift_eq_of_iso_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/a07ba03c-294e-547b-90ae-efb693d4651f
-- title:
--   Overlap isomorphism of local lifts respects the opens Oₐ
-- statement:
--   Let $T' \to T$ be a surjective ring homomorphism $\pi$ of commutative rings whose kernel is a nilpotent ideal, let $f_0 \colon A_0 \to \operatorname{Spec} T$ be a separated morphism of schemes, and let $\mathcal{U}$ be an ordered affine cover of $A_0$, i.e. a finite linearly ordered index type $\iota$ together with opens $U_a \subseteq A_0$, each affine, whose supremum is $\top$. Suppose given for each $a$ a scheme $Y_a$ with a smooth morphism $q_a \colon Y_a \to \operatorname{Spec} T'$ and a morphism $g_a \colon U_a \to Y_a$ making the square with $g_a$, the composite $U_a \hookrightarrow A_0 \to \operatorname{Spec} T$, $q_a$ and $\operatorname{Spec}(\pi)$ a pullback. Suppose also given maps $O_a$ from the opens of $A_0$ to the opens of $Y_a$ satisfying $g_a^{-1}(O_a W) = U_a \cap W$ for all $W$, monotonicity, $O_a(U_a) = \top$, $O_a W \cap O_a W' \le O_a(W \cap W')$, and affineness of $O_a W$ for $W$ affine with $W \le U_a$. Fix indices $a, b$, an isomorphism of schemes $\varphi \colon O_a(U_a \cap U_b) \cong O_b(U_a \cap U_b)$, and morphisms $\gamma, \gamma'$ from $U_a \cap U_b$ to $O_a(U_a \cap U_b)$, $O_b(U_a \cap U_b)$ which, composed with the respective open immersions, equal the restrictions of $g_a$ and $g_b$ along $U_a \cap U_b \le U_a$, $U_a \cap U_b \le U_b$, and which satisfy $\gamma$ followed by $\varphi$ equals $\gamma'$. Then for every open $W \subseteq A_0$ the preimage under $\varphi$ of the open $O_b(U_a \cap U_b) \cap O_b W$ (formed as the preimage of $O_b W$ along the inclusion of $O_b(U_a\cap U_b)$) equals the preimage of $O_a W$ along the inclusion of $O_a(U_a \cap U_b)$. The proof uses neither the smoothness of the $q_a$, nor the separatedness of $f_0$, nor the monotonicity, unit, intersection and affineness properties of the $O_a$.
--
--   This is the compatibility step in the gluing of local smooth lifts of $A_0$ over $\operatorname{Spec} T'$: an isomorphism between the two lifts over the overlap $U_a \cap U_b$ automatically matches up the distinguished opens $O_a W$ and $O_b W$ cut out by an arbitrary open $W$ of $A_0$, so that the gluing data can be compared on smaller opens. It is used in [`AlgebraicGeometry.Smooth.exists_overlap_isos_local_lifts`](thm.html#AlgebraicGeometry.Smooth.exists_overlap_isos_local_lifts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_preimage_opens_local_lift_eq_of_iso_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_opens_local_lift_eq_of_iso_comp_eq
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
    (a b : 𝒰.ι)
    (φ : ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
    (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
    (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b)))
    (hγ : γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a)
    (hγ' : γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b)
    (hφγ : γ ≫ φ.hom = γ') (W : A₀.Opens) :
    φ.hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W := by sorry
