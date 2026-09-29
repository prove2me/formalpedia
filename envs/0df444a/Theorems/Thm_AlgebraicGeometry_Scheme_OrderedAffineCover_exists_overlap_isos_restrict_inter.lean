-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_overlap_isos_restrict_inter
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.exists_overlap_isos_restrict_inter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/59548ef9-a564-5f1c-bed9-e2f3e2ea8ce9
-- title:
--   Restriction of overlap isomorphisms to triple overlaps
-- statement:
--   Let $\pi \colon T' \to T$ be a surjective homomorphism of commutative rings whose kernel is a nilpotent ideal, let $f_0 \colon A_0 \to \operatorname{Spec} T$ be a separated morphism of schemes, and let $\mathcal{U}$ be an ordered affine cover of $A_0$: a finite linearly ordered index type $\iota$ together with opens $U_a \subseteq A_0$ that are affine open and satisfy $\bigsqcup_a U_a = \top$. Suppose given, for each $a$, a scheme $Y_a$ with a smooth morphism $q_a \colon Y_a \to \operatorname{Spec} T'$ and a morphism $g_a \colon U_a \to Y_a$ making the square formed by $g_a$, the composite of the inclusion $U_a \hookrightarrow A_0$ with $f_0$, $q_a$ and $\operatorname{Spec}(\pi)$ a pullback; and an assignment $O_a$ from opens of $A_0$ to opens of $Y_a$ such that $g_a^{-1}(O_a(W))$ is the preimage of $W$ under $U_a \hookrightarrow A_0$, $O_a$ is monotone, $O_a(U_a) = \top$, $O_a(W) \cap O_a(W') \subseteq O_a(W \cap W')$, and $O_a(W)$ is affine open whenever $W$ is affine open with $W \le U_a$. Suppose finally given, for each $a < b$, an isomorphism $\varphi_{ab} \colon O_a(U_a \cap U_b) \cong O_b(U_a \cap U_b)$ such that $\varphi_{ab}$ followed by the inclusion into $Y_b$ and $q_b$ equals the inclusion into $Y_a$ followed by $q_a$; such that the restrictions of $g_a$ and $g_b$ to $U_a \cap U_b$ factor as morphisms $\gamma, \gamma'$ into $O_a(U_a \cap U_b)$, $O_b(U_a \cap U_b)$ with $\gamma$ followed by $\varphi_{ab}$ equal to $\gamma'$; and such that for every open $W$ of $A_0$ the preimage under $\varphi_{ab}$ of the trace of $O_b(W)$ on $O_b(U_a \cap U_b)$ is the trace of $O_a(W)$ on $O_a(U_a \cap U_b)$. Then for every strictly monotone triple $r = (a<b<c)$ in $\iota$, writing $W_r = U_a \cap U_b \cap U_c$, there exist isomorphisms $\rho^{ab}_r \colon O_a(W_r) \cong O_b(W_r)$, $\rho^{bc}_r \colon O_b(W_r) \cong O_c(W_r)$ and $\rho^{ac}_r \colon O_a(W_r) \cong O_c(W_r)$, each compatible with the corresponding $\varphi$ in the sense that composing it with the inclusion of the smaller open into the larger one (given by monotonicity of $O$) agrees with the inclusion followed by $\varphi$, and such that, with $\Gamma(Y_a, O_a(W_r))$ regarded as a $T'$-algebra via $q_a$ and $\operatorname{Spec} \Gamma(Y_a, O_a(W_r))$ identified with the affine open $O_a(W_r)$, both the composite into $Y_c$ given by $\rho^{ac}_r$ and the one given by $\rho^{ab}_r$ followed by $\rho^{bc}_r$ become, after composing with $q_c$, the morphism $\operatorname{Spec}$ of the structure map $T' \to \Gamma(Y_a, O_a(W_r))$, and these two composites agree after precomposition with $\operatorname{Spec}$ of the quotient map $\Gamma(Y_a, O_a(W_r)) \to \Gamma(Y_a, O_a(W_r))/(\ker \pi)\Gamma(Y_a, O_a(W_r))$.
--
--   This is the restriction step in the construction of a global smooth lift of $A_0$ along the nilpotent thickening $T' \to T$ from smooth local lifts $Y_a$: the overlap isomorphisms on double intersections are cut down to the triple intersections, where the two ways of passing from the first to the third chart are shown to be morphisms over $\operatorname{Spec} T'$ that coincide modulo the nilpotent ideal, so that their discrepancy can subsequently be treated as a cocycle with values in a derivation module. It is used by [`AlgebraicGeometry.Smooth.exists_overlap_isos_local_lifts`](thm.html#AlgebraicGeometry.Smooth.exists_overlap_isos_local_lifts), and relies on the affine description of the reduction of a smooth lift provided by [`AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq`](thm.html#AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_overlap_isos_restrict_inter.lean

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

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_overlap_isos_restrict_inter
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
    (φ : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
    (hφq : ∀ (a b : 𝒰.ι) (h : a < b),
      (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
    (hφg : ∀ (a b : 𝒰.ι) (h : a < b),
      ∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
        (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
        γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
        γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
        γ ≫ (φ a b h).hom = γ')
    (hφO : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
      (φ a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W)
    :
    ∃ (ρab : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
      (ρbc : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 1) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
      (ρac : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
      (hρab : ∀ r : 𝒰.Idx 2,
        (ρab r).hom ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) =
          (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) ≫
            (φ (r.1 0) (r.1 1) (r.2 (by decide))).hom)
      (hρbc : ∀ r : 𝒰.Idx 2,
        (ρbc r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) =
          (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) ≫
            (φ (r.1 1) (r.1 2) (r.2 (by decide))).hom)
      (hρac : ∀ r : 𝒰.Idx 2,
        (ρac r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) =
          (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) ≫
            (φ (r.1 0) (r.1 2) (r.2 (by decide))).hom),
      (∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
          (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι) ≫ q (r.1 2) =
        Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))) ∧
      ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
          (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι) ≫ q (r.1 2) =
        Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))))) ∧
      (∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))))) ≫
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
            (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))))) ≫
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
            (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)) := by sorry
