-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt
-- name    : AlgebraicGeometry.SmallExtension.exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/99e653bd-ac73-573d-bf1a-a48a75608f2d
-- title:
--   Push-forward of point derivations along a unit-preserving endomorphism
-- statement:
--   Let $T'$ be a local ring with residue field $k = \mathrm{ResidueField}\,T'$, let $x_k : A_k \to \operatorname{Spec} k$ be a $k$-scheme carrying a relative group law $L_k$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec} k$, with the group axioms and naturality in $T$), let $U_e \subseteq A_k$ be an affine open and $e_1 : \operatorname{Spec} k \to U_e$ a morphism whose composite with the inclusion $U_e \hookrightarrow A_k$ is the unit point $L_k.\mathrm{one}(\mathbb{1})$. Let $W$ be a $k$-vector space together with $\tau_W : W \to \{\varphi : \operatorname{Spec} k[\varepsilon] \to A_k \mid \varphi \circ x_k = \mathrm{tangentBase}\}$ which is injective, has image exactly the tangent vectors at the unit (those $\varphi$ whose reduction along $\mathrm{tangentZero}$ is the unit point), takes addition to $L_k.\mathrm{mul}$ and satisfies $\tau_W(a\cdot v) = \tau_W(v) \circ \mathrm{tangentScale}(a)$. Write $\mathrm{ev} : \Gamma(A_k,U_e) \to k$ for the ring map induced by $e_1$, and $\mathrm{Der}_{\mathrm{ev}}(M)$ for [`Algebra.PointDerivations`](def/Algebra_PointDerivations.html#L9), the $k$-linear maps $D$ with $D(ab) = \mathrm{ev}(a)D(b) + \mathrm{ev}(b)D(a)$, $\Gamma(A_k,U_e)$ being a $k$-algebra via `algebraOfHom`. Let $\Phi_M : \mathrm{Der}_{\mathrm{ev}}(M) \cong W \otimes_k M$ be $k$-linear isomorphisms, natural in $M$ under post-composition, and pinned on dual numbers: whenever $\chi : \Gamma(A_k,U_e) \to k[\varepsilon]$ is a ring map with first component $\mathrm{ev}$ and second component $\delta \in \mathrm{Der}_{\mathrm{ev}}(k)$, the tangent vector $\tau_W$ of $\Phi_k(\delta)$ (under $W \otimes_k k \cong W$) equals $\operatorname{Spec}\chi$ followed by $\mathrm{fromSpec}_{U_e}$. Finally let $\psi : A_k \to A_k$ satisfy $\psi \circ x_k = x_k$ and let $\theta_\psi : W \to W$ be $k$-linear with $\tau_W(\theta_\psi w) = \mathrm{pushPt}\,\psi\,(\tau_W w)$ for all $w$. Then there exists a family of $k$-linear endomorphisms $\eta_M$ of $\mathrm{Der}_{\mathrm{ev}}(M)$, one for each $k$-module $M$, such that: $\eta$ is natural in $M$, commuting with [`Algebra.PointDerivations.map`](def/Algebra_PointDerivations.html#L47) for every $k$-linear $g : M \to M'$; at $M = k$ one has $\Phi_k(\eta_k \delta) = (\theta_\psi \otimes \mathrm{id})\Phi_k(\delta)$; and for every $k$-module $M$ with compatible opposite action (so that $\mathrm{TrivSqZeroExt}\,k\,M$ is a ring), every $\delta \in \mathrm{Der}_{\mathrm{ev}}(M)$ and every ring map $\chi : \Gamma(A_k,U_e) \to \mathrm{TrivSqZeroExt}\,k\,M$ with first component $\mathrm{ev}$ and second component $\delta$, there is a ring map $\chi'$ with first component $\mathrm{ev}$, second component $\eta_M \delta$, and $\operatorname{Spec}\chi'$ followed by $\mathrm{fromSpec}_{U_e}$ equal to $\operatorname{Spec}\chi$ followed by $\mathrm{fromSpec}_{U_e}$ and then $\psi$.
--
--   This is the statement that an endomorphism $\psi$ of a group-law scheme over a field, whose differential at the unit is given by $\theta_\psi$, acts on point derivations at the unit by a family of operators which is natural in the coefficient module, reads as $\theta_\psi \otimes \mathrm{id}$ under the chosen trivialisation $\Phi$, and is realised on $\mathrm{TrivSqZeroExt}\,k\,M$-valued points by post-composition with $\psi$. It is used in the comparison of tangent coordinates attached to a pair at a point, within the deformation-theoretic infrastructure for small extensions and Néron models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt.lean

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

theorem AlgebraicGeometry.SmallExtension.exists_pointDerivations_pushforward_natural_of_forall_apply_eq_pushPt
    (T' : Type u) [CommRing T'] [IsLocalRing T']

    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

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
    (θψ : W →ₗ[(ResidueField T')] W) (hθψ : ∀ w : W, τW (θψ w) = pushPt ψ hψ (τW w)) :
    letI := algebraOfHom xk Ue
    ∃ η : ∀ (M : Type u) [AddCommGroup M] [Module (ResidueField T') M], ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) M) →ₗ[(ResidueField T')] ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) M),

      (∀ (M M' : Type u) [AddCommGroup M] [Module (ResidueField T') M] [AddCommGroup M'] [Module (ResidueField T') M']
          (g : M →ₗ[(ResidueField T')] M') (δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) M)),
        η M' (Algebra.PointDerivations.map ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) g δ) = Algebra.PointDerivations.map ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) g (η M δ)) ∧

      (∀ δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) (ResidueField T')),
        Φ (ResidueField T') (η (ResidueField T') δ) =
          TensorProduct.map θψ (LinearMap.id : (ResidueField T') →ₗ[(ResidueField T')] (ResidueField T')) (Φ (ResidueField T') δ)) ∧

      (∀ (M : Type u) [AddCommGroup M] [Module (ResidueField T') M] [Module (ResidueField T')ᵐᵒᵖ M] [IsCentralScalar (ResidueField T') M]
          (χ : Γ(Ak, Ue) →+* TrivSqZeroExt (ResidueField T') M) (δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) M)),
        (∀ a : Γ(Ak, Ue), TrivSqZeroExt.fst (χ a) = ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) a) →
        (∀ a : Γ(Ak, Ue), TrivSqZeroExt.snd (χ a) = δ.1 a) →
        ∃ χ' : Γ(Ak, Ue) →+* TrivSqZeroExt (ResidueField T') M,
          (∀ a : Γ(Ak, Ue), TrivSqZeroExt.fst (χ' a) = ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) a) ∧
          (∀ a : Γ(Ak, Ue), TrivSqZeroExt.snd (χ' a) = (η M δ).1 a) ∧
          Spec.map (CommRingCat.ofHom χ') ≫ hUe.fromSpec = Spec.map (CommRingCat.ofHom χ) ≫ hUe.fromSpec ≫ ψ) := by sorry
