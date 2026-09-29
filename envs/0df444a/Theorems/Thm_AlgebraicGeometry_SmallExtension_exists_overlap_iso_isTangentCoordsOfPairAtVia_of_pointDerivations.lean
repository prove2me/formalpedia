-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_overlap_iso_isTangentCoordsOfPairAtVia_of_pointDerivations
-- name    : AlgebraicGeometry.SmallExtension.exists_overlap_iso_isTangentCoordsOfPairAtVia_of_pointDerivations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/8f6dcbe0-56d9-5de2-902f-4e29c8912a4e
-- title:
--   Twisting an overlap isomorphism by a point derivation
-- statement:
--   Let $\pi:T'\to T$ be a surjection of commutative rings with $T'$ local artinian, with nilpotent kernel $I=\ker\pi$ satisfying $I\cdot\mathfrak m_{T'}=0$ and $I\subseteq\mathfrak m_{T'}$; let $V$ be a finite module over $k=\mathrm{ResidueField}\,T'$, also a $T'$-module compatibly (with the central right action), and let $\iota:V\to T'$ be an injective $T'$-linear map whose image is $I$. Given $f_0:A_0\to\operatorname{Spec}T$, opens $U_a,U_b\subseteq A_0$, morphisms $q_a:Y_a\to\operatorname{Spec}T'$ with $q_a$ smooth and $q_b:Y_b\to\operatorname{Spec}T'$, lifts $g_a:U_a\to Y_a$, $g_b:U_b\to Y_b$ with $(g_b,U_b\hookrightarrow A_0\to\operatorname{Spec}T)$ cartesian over $\operatorname{Spec}(\pi)$, assignments of opens $O_a,O_b$ on $A_0$ with $g_b^{-1}O_b(W)=U_b\cap W$ and $O_a(U_a\cap U_b)$, $O_b(U_a\cap U_b)$ affine; further $f_k:A_k\to\operatorname{Spec}k$ with a relative group law $L_k$ (functorial multiplication, unit, inverse on points over $\operatorname{Spec}k$, with the group axioms and naturality), an open $W\subseteq A_k$ and $a_W:W\to Y_b$ cartesian over $\operatorname{Spec}(\mathrm{residue}\,T')$, an affine open $U_e\subseteq A_k$ and $e_1:\operatorname{Spec}k\to U_e$ whose composite with $U_e\hookrightarrow A_k$ is the unit of $L_k$. Let $\varphi:O_a(U_a\cap U_b)\cong O_b(U_a\cap U_b)$ satisfy: it is over $T'$ (i.e. $\varphi$ followed by the inclusion and $q_b$ equals the inclusion followed by $q_a$); the restrictions of $g_a$ and $g_b$ to $U_a\cap U_b$ factor through these opens as $\gamma,\gamma'$ with $\gamma$ followed by $\varphi$ equal to $\gamma'$; and $\varphi^{-1}$ of the trace of $O_b(W')$ equals the trace of $O_a(W')$ for every open $W'$. Write $C=\Gamma(Y_a,O_a(U_a\cap U_b))$, a $T'$-algebra via $q_a$, and $\Gamma(A_k,U_e)$ a $k$-algebra via $f_k$. Finally let $\delta$ be a point derivation at the unit, i.e. a $k$-linear map $\Gamma(A_k,U_e)\to\operatorname{Hom}_k(V^\vee,k\otimes_{T'}C)$ with $\delta(ab)=\mathrm{ev}(a)\delta(b)+\mathrm{ev}(b)\delta(a)$, $\mathrm{ev}$ being evaluation at $e_1$. Then there is a second isomorphism $\varphi':O_a(U_a\cap U_b)\cong O_b(U_a\cap U_b)$ with the same three properties (over $T'$, carrying the restriction of $g_a$ to that of $g_b$, and matching the $O$-opens), such that `IsTangentCoordsOfPairAtVia` holds for $I$, $V$, $\iota$, $C$, the two $T'$-points $u_\psi=\mathrm{isoSpec}^{-1}$ followed by $\psi$ and $O_b(U_a\cap U_b)\hookrightarrow Y_b$ for $\psi=\varphi,\varphi'$, the data $f_k,L_k,W,a_W,U_e$ and the coordinate function $\delta$: that is, there are $w_0:\operatorname{Spec}(\mathrm{thickening}\,T'\,V\,C)\to W$ lying over the relative tangent base of $\mathrm{thickeningSnd}$ and $w_1:\operatorname{Spec}(\mathrm{thickening}\,T'\,V\,C)\to U_e$ such that $w_0$ followed by $a_W$ exhibits the pair $(u_\varphi,u_{\varphi'})$ as a tangent vector (a Schlessinger map $\vartheta$ from the pair ring of $I$ and $C$ to the thickening, together with a morphism from the spectrum of the pair ring to $Y_b$ pulling back to $u_\varphi$ and $u_{\varphi'}$ along the two projections and to $w_0\circ a_W$ along $\vartheta$), $w_1$ followed by $U_e\hookrightarrow A_k$ is the $L_k$-translate of $w_0$ followed by $W\hookrightarrow A_k$, and $\delta$ equals the tangent coordinates of the chart homomorphism of $w_1$.
--
--   This is the deformation-theoretic twisting step: over a small extension $T'\to T$ the liftings of a fixed reduction form a torsor under a group of derivations, and here one prescribed point derivation $\delta$ at the unit of the special-fibre group law is realised by replacing an overlap isomorphism $\varphi$ of two local smooth lifts by a new one $\varphi'$ whose tangent coordinates relative to $\varphi$ are exactly $\delta$. It is used by [`AlgebraicGeometry.SmallExtension.exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary`](thm.html#AlgebraicGeometry.SmallExtension.exists_overlap_isos_cocycle_of_pointDerivations_two_coboundary), where such twists on each overlap of a two-chart cover are assembled to modify a gluing cocycle by a prescribed coboundary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_overlap_iso_isTangentCoordsOfPairAtVia_of_pointDerivations.lean

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

theorem AlgebraicGeometry.SmallExtension.exists_overlap_iso_isTangentCoordsOfPairAtVia_of_pointDerivations
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    (hI : RingHom.ker π ≤ maximalIdeal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T))
    (Ua Ub : A₀.Opens)
    {Ya Yb : Scheme.{u}} (qa : Ya ⟶ Spec (CommRingCat.of T')) (qb : Yb ⟶ Spec (CommRingCat.of T')) (hqa : Smooth qa)
    (ga : (↑Ua : Scheme.{u}) ⟶ Ya) (gb : (↑Ub : Scheme.{u}) ⟶ Yb)
    (hgb : IsPullback gb (Ub.ι ≫ f₀) qb (Spec.map (CommRingCat.ofHom π)))
    (Oa : A₀.Opens → Ya.Opens) (Ob : A₀.Opens → Yb.Opens)
    (hOb : ∀ W : A₀.Opens, gb ⁻¹ᵁ Ob W = Ub.ι ⁻¹ᵁ W)
    (hOaffa : IsAffineOpen (Oa (Ua ⊓ Ub))) (hOaffb : IsAffineOpen (Ob (Ua ⊓ Ub)))

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') fk)
    (W : Ak.Opens) (aW : (W : Scheme.{u}) ⟶ Yb)
    (haW : IsPullback aW (W.ι ≫ fk) qb (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    (φ : (↑(Oa (Ua ⊓ Ub)) : Scheme.{u}) ≅ ↑(Ob (Ua ⊓ Ub)))
    (hφq : φ.hom ≫ (Ob (Ua ⊓ Ub)).ι ≫ qb = (Oa (Ua ⊓ Ub)).ι ≫ qa)
    (hφg : ∃ (γ : (↑(Ua ⊓ Ub) : Scheme.{u}) ⟶ ↑(Oa (Ua ⊓ Ub))) (γ' : (↑(Ua ⊓ Ub) : Scheme.{u}) ⟶ ↑(Ob (Ua ⊓ Ub))),
        γ ≫ (Oa (Ua ⊓ Ub)).ι = A₀.homOfLE inf_le_left ≫ ga ∧
        γ' ≫ (Ob (Ua ⊓ Ub)).ι = A₀.homOfLE inf_le_right ≫ gb ∧
        γ ≫ φ.hom = γ')
    (hφO : ∀ W' : A₀.Opens, φ.hom ⁻¹ᵁ ((Ob (Ua ⊓ Ub)).ι ⁻¹ᵁ Ob W') = (Oa (Ua ⊓ Ub)).ι ⁻¹ᵁ Oa W')

    (δ : letI := algebraOfHom qa (Oa (Ua ⊓ Ub)); letI := algebraOfHom fk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(Ya, Oa (Ua ⊓ Ub)))))) :
    letI := algebraOfHom qa (Oa (Ua ⊓ Ub)); letI := algebraOfHom fk Ue
    ∃ φ' : (↑(Oa (Ua ⊓ Ub)) : Scheme.{u}) ≅ ↑(Ob (Ua ⊓ Ub)),
      φ'.hom ≫ (Ob (Ua ⊓ Ub)).ι ≫ qb = (Oa (Ua ⊓ Ub)).ι ≫ qa ∧
      (∃ (γ : (↑(Ua ⊓ Ub) : Scheme.{u}) ⟶ ↑(Oa (Ua ⊓ Ub))) (γ' : (↑(Ua ⊓ Ub) : Scheme.{u}) ⟶ ↑(Ob (Ua ⊓ Ub))),
        γ ≫ (Oa (Ua ⊓ Ub)).ι = A₀.homOfLE inf_le_left ≫ ga ∧
        γ' ≫ (Ob (Ua ⊓ Ub)).ι = A₀.homOfLE inf_le_right ≫ gb ∧
        γ ≫ φ'.hom = γ') ∧
      (∀ W' : A₀.Opens, φ'.hom ⁻¹ᵁ ((Ob (Ua ⊓ Ub)).ι ⁻¹ᵁ Ob W') = (Oa (Ua ⊓ Ub)).ι ⁻¹ᵁ Oa W') ∧
      IsTangentCoordsOfPairAtVia (RingHom.ker π) V ι Γ(Ya, Oa (Ua ⊓ Ub))
        (hOaffa.isoSpec.inv ≫ φ.hom ≫ (Ob (Ua ⊓ Ub)).ι)
        (hOaffa.isoSpec.inv ≫ φ'.hom ≫ (Ob (Ua ⊓ Ub)).ι)
        fk Lk W aW Ue
        (fun x => (δ : Γ(Ak, Ue) →ₗ[ResidueField T']
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(Ya, Oa (Ua ⊓ Ub))))) x) := by sorry
