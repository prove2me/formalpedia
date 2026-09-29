-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_forall_apply_eq_pushPt_of_mul_maximalIdeal_eq_bot
-- name    : AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_forall_apply_eq_pushPt_of_mul_maximalIdeal_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/c6bc4dde-4e99-567a-a3bd-28b372d1bf9e
-- title:
--   Chain rule for tangent coordinates under an endomorphism
-- statement:
--   Let $T'$ be a local commutative ring with residue field $k$, let $I\subseteq T'$ be an ideal with $I\le\mathfrak m_{T'}$ and $I\cdot\mathfrak m_{T'}=0$, let $V$ be a finite-dimensional $k$-vector space carrying a compatible $T'$-module structure (with the right action central) together with a $T'$-linear map $\iota:V\to T'$, and let $C$ be a $T'$-algebra. Let $z:U\to Y$ and $z':U\to Y'$ be morphisms of schemes and $u,v:\operatorname{Spec}C\to U$ two points that agree after restriction along $C\to C/IC$. On the special fibre, let $x_k:A_k\to\operatorname{Spec}k$ carry a relative group law $L_k$, let $U_e\subseteq A_k$ be an affine open containing the unit through $e_1$ (i.e. $e_1$ followed by the inclusion is $(L_k.\mathrm{one}(\mathbb 1))_1$), and let $a_k:A_k\to Y$, $a_k':A_k\to Y'$. Let $W$ be a $k$-module with an injective parametrisation $\tau_W$ of the dual-number points of $x_k$ whose image is exactly the tangent vectors for $L_k$, additive for $L_k.\mathrm{mul}$ and homogeneous for `tangentScale`, and let $\Phi_M:\mathrm{PointDerivations}_k(\Gamma(A_k,U_e),\mathrm{ev}_{e_1};M)\cong W\otimes_kM$ be a family of $k$-linear isomorphisms natural in $M$ and pinned on $k[\varepsilon]$-points: whenever $\chi:\Gamma(A_k,U_e)\to k[\varepsilon]$ is a ring homomorphism with first component $\mathrm{ev}_{e_1}$ and second component $\delta$, the point $\tau_W$ of $\Phi_k(\delta)$ (read through $W\otimes_kk\cong W$) is $\operatorname{Spec}\chi$ followed by $U_e$'s canonical map from its spectrum. Let $\psi:A_k\to A_k$ be a morphism over $\operatorname{Spec}k$ which is a homomorphism for $L_k$ on all test objects (`pushPt` of $\psi$ commutes with $L_k.\mathrm{mul}$), with differential $\theta_\psi\in\mathrm{End}_k(W)$ characterised by $\tau_W(\theta_\psi w)=\mathrm{pushPt}\,\psi\,(\tau_W w)$, and assume that for every scheme $S$ and $g:S\to U$, $g_k:S\to A_k$ with $g$ followed by $z$ equal to $g_k$ followed by $a_k$, one has $g$ followed by $z'$ equal to $g_k$ followed by $\psi$ and then $a_k'$. Finally let $\delta$ be a point derivation of $\Gamma(A_k,U_e)$ at the unit with values in $\mathrm{Hom}_k(V^\vee,k\otimes_{T'}C)$ such that its underlying function satisfies `IsTangentCoordsOfPairAt` for the pair $(u\,z,v\,z)$ into $Y$ relative to $x_k,L_k,a_k,U_e$ — that is, there are a thickened point $w_0$ of $A_k$ over the relative tangent base, with $(w_0$ followed by $a_k)$ a tangent datum `IsTangentOfPair` for $u,v$, and a lift $w_1$ into $U_e$ of the $L_k$-translate of $w_0$, for which $\delta$ is the chart-read tangent coordinate function. Then the function obtained by applying $\Phi^{-1}$ to $(\theta_\psi\otimes\mathrm{id})\,\Phi(\delta)$ satisfies the same predicate for the pair $(u\,z',v\,z')$ into $Y'$, relative to $x_k,L_k,a_k',U_e$.
--
--   This is the chain rule for the canonical tangent coordinates of a pair of lifts agreeing modulo a square-zero ideal: replacing the target morphism $z$ by one that factors through the group endomorphism $\psi$ on the special fibre transforms the coordinate derivation by the differential $\theta_\psi$ of $\psi$, tensored with the identity of the coefficient module. It is used in the bare-deformation computations comparing local lifts and their obstruction cocycles, where $\psi$ is an untwisting or translation automorphism of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_forall_apply_eq_pushPt_of_mul_maximalIdeal_eq_bot.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct
  AlgebraicGeometry.SmallExtension CerednikDrinfeld.QM Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_forall_apply_eq_pushPt_of_mul_maximalIdeal_eq_bot
    (T' : Type u) [CommRing T'] [IsLocalRing T'] (I : Ideal T')

    (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)

    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T')

    (C : Type u) [CommRing C] [Algebra T' C]
    {U Y Y' : Scheme.{u}} (z : U ⟶ Y) (z' : U ⟶ Y') (u v : Spec (CommRingCat.of C) ⟶ U)

    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)

    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (ak : Ak ⟶ Y) (ak' : Ak ⟶ Y')

    (W : Type u) [AddCommGroup W] [Module (ResidueField T') W]
    (τW : W → SchemeHomOver (tangentBase (ResidueField T') (RingHom.id (ResidueField T'))) xk)
    (hWinj : Function.Injective τW)
    (hWrange : ∀ P : SchemeHomOver (tangentBase (ResidueField T') (RingHom.id (ResidueField T'))) xk, P ∈ Set.range τW ↔ IsTangentVector Lk (ResidueField T') (RingHom.id (ResidueField T')) P)
    (hWadd : ∀ v w : W, τW (v + w) = Lk.mul (tangentBase (ResidueField T') (RingHom.id (ResidueField T'))) (τW v) (τW w))
    (hWsmul : ∀ (a : (ResidueField T')) (v : W), (τW (a • v)).1 = tangentScale (ResidueField T') a ≫ (τW v).1)

    (Φ : letI := algebraOfHom xk Ue
      ∀ (M : Type u) [AddCommGroup M] [Module (ResidueField T') M], ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) M) ≃ₗ[(ResidueField T')] (W ⊗[(ResidueField T')] M))
    (hΦnat : letI := algebraOfHom xk Ue
      ∀ (M M' : Type u) [AddCommGroup M] [Module (ResidueField T') M] [AddCommGroup M'] [Module (ResidueField T') M'] (g : M →ₗ[(ResidueField T')] M') (δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) M)),
        Φ M' (Algebra.PointDerivations.map ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) g δ) = TensorProduct.map (LinearMap.id : W →ₗ[(ResidueField T')] W) g (Φ M δ))
    (hΦpin : letI := algebraOfHom xk Ue
      ∀ (δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) (ResidueField T'))) (χ : Γ(Ak, Ue) →+* DualNumber (ResidueField T')),
        (∀ a : Γ(Ak, Ue), TrivSqZeroExt.fst (χ a) = ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) a) →
        (∀ a : Γ(Ak, Ue), TrivSqZeroExt.snd (χ a) = (δ : Γ(Ak, Ue) →ₗ[(ResidueField T')] (ResidueField T')) a) →
        (τW (TensorProduct.rid (ResidueField T') W (Φ (ResidueField T') δ))).1 = Spec.map (CommRingCat.ofHom χ) ≫ hUe.fromSpec)

    (ψ : Ak ⟶ Ak) (hψ : ψ ≫ xk = xk)
    (hψhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t xk),
      pushPt ψ hψ (Lk.mul t P Q) = Lk.mul t (pushPt ψ hψ P) (pushPt ψ hψ Q))
    (θψ : W →ₗ[(ResidueField T')] W) (hθψ : ∀ w : W, τW (θψ w) = pushPt ψ hψ (τW w))

    (hzψ : ∀ {S : Scheme.{u}} (g : S ⟶ U) (gk : S ⟶ Ak), g ≫ z = gk ≫ ak → g ≫ z' = gk ≫ ψ ≫ ak')

    (δ : letI := algebraOfHom xk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] C))))
    (hδ : letI := algebraOfHom xk Ue
      IsTangentCoordsOfPairAt I V ι C (u ≫ z) (v ≫ z) xk Lk ak Ue (fun a => δ.1 a)) :
    letI := algebraOfHom xk Ue
    IsTangentCoordsOfPairAt I V ι C (u ≫ z') (v ≫ z') xk Lk ak' Ue
      (fun a => ((Φ (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] C))).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] C)) →ₗ[(ResidueField T')] (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] C))) (Φ (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] C)) δ))).1 a) := by sorry
