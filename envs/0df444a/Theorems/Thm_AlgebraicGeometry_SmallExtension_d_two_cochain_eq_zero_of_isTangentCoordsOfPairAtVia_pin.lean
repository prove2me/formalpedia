-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_d_two_cochain_eq_zero_of_isTangentCoordsOfPairAtVia_pin
-- name    : AlgebraicGeometry.SmallExtension.d_two_cochain_eq_zero_of_isTangentCoordsOfPairAtVia_pin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/de85a270-0c3c-5a09-bc9b-a8f863c7fbdf
-- title:
--   Pinned obstruction 2-cochain is a Čech cocycle
-- statement:
--   Let $\pi \colon T' \to T$ be a surjective homomorphism of commutative rings with $T'$ Artinian local, let $\ker\pi$ be nilpotent, contained in the maximal ideal $\mathfrak m_{T'}$ and satisfy $(\ker\pi)\,\mathfrak m_{T'} = 0$; let $f_0 \colon A_0 \to \operatorname{Spec} T$ be separated and smooth, let $\rho \colon T \to k := \operatorname{ResidueField} T'$ satisfy $\rho\circ\pi = \mathrm{residue}$, and let $V$ be a finite-dimensional $k$-vector space, also a $T'$-module compatibly, with $\iota \colon V \to T'$ an injective $T'$-linear map whose image is $\ker\pi$. Further data: an ordered affine cover $\mathcal U$ of $A_0$ (finite linearly ordered index set, affine opens $U_a$ with supremum $\top$); for each $a$ a smooth $q_a \colon Y_a \to \operatorname{Spec} T'$ and $g_a \colon U_a \to Y_a$ making $U_a$ the base change of $Y_a$ along $\operatorname{Spec}\pi$; a separated $f_k \colon A_k \to \operatorname{Spec} k$ with a relative group law $L_k$, an affine morphism $i_0 \colon A_k \to A_0$ exhibiting $A_k$ as the base change of $f_0$ along $\operatorname{Spec}\rho$, an affine open $U_e \subseteq A_k$ and a point $e_1$ of $U_e$ lying over the unit section of $L_k$; maps $O_a$ from opens of $A_0$ to opens of $Y_a$ with $g_a^{-1}O_a(W) = U_a \cap W$, monotone, $O_a(U_a) = \top$, $O_a(W)\cap O_a(W') \le O_a(W\cap W')$ and preserving affineness of opens below $U_a$; for every strictly monotone simplex $s$ a ring isomorphism $\sigma_s \colon k \otimes_{T'} \Gamma(Y_{s_0}, O_{s_0}(\bigcap_j U_{s_j})) \cong \Gamma(A_k, \bigcap_j i_0^{-1}U_{s_j})$, pinned geometrically by $h\sigma_1$ to the comparison map into $Y_{s_0}$ and $k$-linear in the sense $\sigma_s(x\otimes 1) =$ image of $x$; for $a<b$ an isomorphism $\varphi_{ab} \colon O_a(U_a\cap U_b) \cong O_b(U_a\cap U_b)$ over $T'$, carrying the restrictions of $g_a$ to those of $g_b$ and compatible with the $O$'s on preimages; and for each $2$-simplex $r = (a<b<c)$ isomorphisms $\rho_{ab}, \rho_{bc}, \rho_{ac}$ between the triple-overlap opens compatible with the corresponding $\varphi$'s. Finally, let $\omega$ be a point derivation of $\Gamma(A_k, U_e)$ at $e_1$ (a $k$-linear $D$ with $D(ab) = e_1^*(a)D(b) + e_1^*(b)D(a)$) valued in $\operatorname{Hom}_k\bigl(V^\vee, \check C^2(i_0^{-1}\mathcal U, \mathcal O_{A_k})\bigr)$, pinned as follows: for every $2$-simplex $r$ there is $c_s \colon \Gamma(A_k, U_e) \to \operatorname{Hom}_k(V^\vee, k\otimes_{T'}\Gamma(Y_{r_0}, O_{r_0}(\bigcap U_{r_j})))$ which is a system of tangent coordinates, in the sense of `IsTangentCoordsOfPairAtVia` for $\ker\pi$, $V$, $\iota$, of the pair of maps from the affine chart to $O_{r_2}(\bigcap U_{r_j})$ given by $\rho_{ac}$ and by $\rho_{ab}$ followed by $\rho_{bc}$, relative to $f_k$, $L_k$, the open $i_0^{-1}U_{r_2}$ with its comparison map to $Y_{r_2}$, and $U_e$, and such that $\sigma_r(c_s(a)(\xi))$ equals the value at $r$ of $\omega(a)(\xi)$. The conclusion is that for all $a \in \Gamma(A_k, U_e)$ and all $\xi \in V^\vee$ the Čech differential in degree $2$ of the $2$-cochain $\omega(a)(\xi)$, for the structure presheaf of $A_k$ and the cover $i_0^{-1}\mathcal U$, vanishes.
--
--   This is the cocycle step in the construction of the obstruction class to lifting a smooth separated scheme across a small extension of Artinian local rings: the $2$-cochain assembled from the canonical tangent coordinates of the pairs of triple-overlap comparison isomorphisms is closed, so it represents a class in $H^2$ of the cover. It is used by [`AlgebraicGeometry.SmallExtension.exists_pointDerivations_obstruction_two_cocycle_of_local_lifts`](thm.html#AlgebraicGeometry.SmallExtension.exists_pointDerivations_obstruction_two_cocycle_of_local_lifts), which packages the obstruction cochain together with this cocycle property.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_d_two_cochain_eq_zero_of_isTangentCoordsOfPairAtVia_pin.lean

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

theorem AlgebraicGeometry.SmallExtension.d_two_cochain_eq_zero_of_isTangentCoordsOfPairAtVia_pin
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀] [Smooth f₀]

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) [IsSeparated fk]
    (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) [IsAffineHom i₀] (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W'))
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W))

    (σ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      ((ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))) ≃+* Γ(Ak, (𝒰.comap i₀).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒰.Idx n),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      (Scheme.OrderedAffineCover.isAffineOpen_inter fk (𝒰.comap i₀) s).isoSpec.hom ≫
          Spec.map (CommRingCat.ofHom (σ s).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)) →ₐ[T']
              (ResidueField T') ⊗[T'] Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s))).toRingHom) ≫
          (hOaff (s.1 0) (𝒰.inter s) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 s) (𝒰.inter_le s 0)).fromSpec =
        Ak.homOfLE (𝒰.comap_inter_le i₀ s) ≫ (i₀ ∣_ 𝒰.inter s) ≫ A₀.homOfLE (𝒰.inter_le s 0) ≫ g (s.1 0))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒰.Idx n) (x : ResidueField T'),
      letI := algebraOfHom (q (s.1 0)) (O (s.1 0) (𝒰.inter s))
      letI := algebraOfHom fk ((𝒰.comap i₀).inter s)
      σ s (x ⊗ₜ[T'] (1 : Γ(Y (s.1 0), O (s.1 0) (𝒰.inter s)))) = algebraMap (ResidueField T') Γ(Ak, (𝒰.comap i₀).inter s) x)

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

    (ρab : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
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
          (φ (r.1 0) (r.1 2) (r.2 (by decide))).hom)
    (ω : letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 2)))
    (hω : ∀ r : 𝒰.Idx 2,
      letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
      letI := algebraOfHom fk Ue
      ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
                ((ResidueField T') ⊗[T'] Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))),
        IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)
          fk Lk (i₀ ⁻¹ᵁ 𝒰.U (r.1 2)) ((i₀ ∣_ 𝒰.U (r.1 2)) ≫ g (r.1 2)) Ue cs ∧
        ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ r (cs a ξ) = ω.1 a ξ r) :
    letI := algebraOfHom fk Ue
    ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
    (OModulePresheaf.unit fk).d (𝒰.comap i₀) 2 (ω.1 a ξ) = 0 := by sorry
