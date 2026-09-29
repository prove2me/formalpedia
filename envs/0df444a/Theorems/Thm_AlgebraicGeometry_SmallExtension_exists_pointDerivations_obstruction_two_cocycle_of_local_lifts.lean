-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_pointDerivations_obstruction_two_cocycle_of_local_lifts
-- name    : AlgebraicGeometry.SmallExtension.exists_pointDerivations_obstruction_two_cocycle_of_local_lifts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/90659706-f4a7-55f5-b2b7-f9c39a81f7a3
-- title:
--   Obstruction 2-cocycle of a system of local smooth lifts
-- statement:
--   Let $T'$ be an Artinian local ring with residue field $k=\mathrm{ResidueField}\,T'$, let $\pi\colon T'\to T$ be a surjective ring homomorphism with nilpotent kernel such that $\ker\pi\cdot\mathfrak m_{T'}=0$ and $\ker\pi\subseteq\mathfrak m_{T'}$, and let $\rho\colon T\to k$ satisfy $\rho\circ\pi=\mathrm{residue}$. Let $f_0\colon A_0\to\operatorname{Spec} T$ be separated and smooth. Let $V$ be a finite-dimensional $k$-vector space, also a $T'$-module compatibly with the $k$-action, and $\iota\colon V\to T'$ an injective $T'$-linear map whose range is $\ker\pi$. Let $\mathcal U$ be an ordered affine cover of $A_0$ (a finite linearly ordered index set $\mathcal U.\iota$, affine opens $U_a$ with $\bigsqcup_a U_a=\top$), and for each $a$ let $q_a\colon Y_a\to\operatorname{Spec} T'$ be smooth together with $g_a\colon U_a\to Y_a$ making $(g_a,\,U_a\hookrightarrow A_0\xrightarrow{f_0}\operatorname{Spec}T,\,q_a,\,\operatorname{Spec}\pi)$ cartesian: a system of local lifts. Let $f_k\colon A_k\to\operatorname{Spec}k$ be separated, $L_k$ a relative group law on $f_k$ (functorial multiplication, unit and inverse on points over the base, with associativity, unit and inverse laws and naturality of multiplication), $i_0\colon A_k\to A_0$ an affine morphism making $A_k$ the base change of $f_0$ along $\operatorname{Spec}\rho$, and $U_e\subseteq A_k$ an affine open through which the unit section $(L_k.\mathrm{one}(\mathbf 1)).1$ factors via $e_1$. Then there exist: (i) for each $a$ an assignment $W\mapsto O_a(W)$ from opens of $A_0$ to opens of $Y_a$ with $g_a^{-1}O_a(W)=W\cap U_a$, monotone, $O_a(U_a)=\top$, $O_a(W)\cap O_a(W')\le O_a(W\cap W')$, and $O_a(W)$ affine whenever $W\le U_a$ is affine; (ii) for every strictly increasing chain $s=(a_0<\dots<a_n)$ a ring isomorphism $\sigma_s\colon k\otimes_{T'}\Gamma(Y_{a_0},O_{a_0}(U_s))\xrightarrow{\ \sim\ }\Gamma(A_k,i_0^{-1}U_s)$, where $U_s=\bigcap_j U_{a_j}$, such that $\operatorname{Spec}$ of $\sigma_s$ composed with the right inclusion into the tensor product identifies the affine scheme $i_0^{-1}U_s$ with the restriction of $i_0$ followed by $g_{a_0}$ into $O_{a_0}(U_s)$, and such that $\sigma_s(x\otimes 1)$ is the image of $x\in k$ under the structure map; (iii) for $a<b$ isomorphisms $\varphi_{ab}\colon O_a(U_a\cap U_b)\cong O_b(U_a\cap U_b)$ over $\operatorname{Spec}T'$, compatible with $g_a,g_b$ on $U_a\cap U_b$ and with the opens $O_a(W)$, $O_b(W)$; (iv) for every triple $r=(a_0<a_1<a_2)$ isomorphisms $\rho^{ab}_r,\rho^{bc}_r,\rho^{ac}_r$ between the lifts $O_{a_i}(U_r)$ of the triple overlap, each compatible with the corresponding $\varphi$ after restriction; and (v) a point-derivation $\omega$ on $\Gamma(A_k,U_e)$ at the $k$-point given by $e_1$, with values in $k$-linear maps from $V^\vee$ to the degree-$2$ Čech cochains of the unit $\mathcal O$-module presheaf of $f_k$ for the cover $i_0^{-1}\mathcal U$ (that is, a $k$-linear $\omega$ with $\omega(ab)=e_1^\ast(a)\,\omega(b)+e_1^\ast(b)\,\omega(a)$), such that: for every triple $r$ there are tangent coordinates $cs$ on $\Gamma(A_k,U_e)$ with values in $V^\vee\to k\otimes_{T'}\Gamma(Y_{a_0},O_{a_0}(U_r))$ satisfying the predicate `IsTangentCoordsOfPairAtVia` for $\ker\pi$, $V$, $\iota$ and the two maps $\operatorname{Spec}\Gamma(Y_{a_0},O_{a_0}(U_r))\to O_{a_2}(U_r)$ given by $\rho^{ac}_r$ and by $\rho^{ab}_r$ followed by $\rho^{bc}_r$ — that is, there are maps $w_0$ into $i_0^{-1}U_{a_2}$ over the base and $w_1$ into $U_e$ such that $w_0$ followed by the restriction of $i_0$ and $g_{a_2}$ exhibits a tangent vector of the pair, $w_1$ is the $L_k$-translate of $w_0$ to the unit, and $cs$ is read off from $w_1$ by the chart ring homomorphism on $\Gamma(A_k,U_e)$ — and $\sigma_r(cs(a)(\xi))=\omega(a)(\xi)(r)$ for all $a\in\Gamma(A_k,U_e)$, $\xi\in V^\vee$; and the Čech differential of $\omega(a)(\xi)$ in degree $2$ vanishes for all $a$ and $\xi$.
--
--   This is the existence half of the Čech obstruction theory for lifting a smooth separated scheme along a small extension, in degree $2$ and expressed in tangent coordinates at the unit of a relative group law on the special fibre: the triple-overlap discrepancies of a system of local smooth lifts are packaged as a point-derivation valued in degree-$2$ cochains, and that cochain is shown to be a cocycle. It is used in the construction of smooth lifts of abelian schemes along small surjections, where the vanishing of this class is compared with a Čech-dimension bound.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_pointDerivations_obstruction_two_cocycle_of_local_lifts.lean

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

theorem AlgebraicGeometry.SmallExtension.exists_pointDerivations_obstruction_two_cocycle_of_local_lifts
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
    :
    ∃
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
            (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit fk).cochain (𝒰.comap i₀) 2))),
      (∀ r : 𝒰.Idx 2,
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
          ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ r (cs a ξ) = ω.1 a ξ r) ∧
      (letI := algebraOfHom fk Ue
        ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
          (OModulePresheaf.unit fk).d (𝒰.comap i₀) 2 (ω.1 a ξ) = 0) := by sorry
