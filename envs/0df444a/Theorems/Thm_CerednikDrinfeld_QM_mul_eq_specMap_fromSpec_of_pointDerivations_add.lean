-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_mul_eq_specMap_fromSpec_of_pointDerivations_add
-- name    : CerednikDrinfeld.QM.mul_eq_specMap_fromSpec_of_pointDerivations_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/ce989201-0942-5619-b20f-8c7455d0f653
-- title:
--   The group law adds point derivations at the unit
-- statement:
--   Let $\kappa$ be a field, let $X$ be a scheme with a morphism $f_X \colon X \to \operatorname{Spec}\kappa$, and let $L$ be a relative group law on $f_X$ over $\kappa$: functorial multiplication, unit and inverse operations on the $T$-points $\{\varphi \colon T \to X \mid \varphi \text{ followed by } f_X = t\}$ for every $t \colon T \to \operatorname{Spec}\kappa$, satisfying associativity, both unit laws, left inverse, and naturality in the test scheme. Let $U \subseteq X$ be an affine open and let $e_1 \colon \operatorname{Spec}\kappa \to U$ be such that $e_1$ followed by the inclusion $U \hookrightarrow X$ is the underlying morphism of the unit of $L$ at the test object $\operatorname{Spec}\kappa$ with structure morphism the identity. Give $\Gamma(X,U)$ the $\kappa$-algebra structure induced by $f_X$, and write $\mathrm{ev} \colon \Gamma(X,U) \to \kappa$ for the ring homomorphism obtained from $e_1$ on global sections, composed with the canonical identifications. The assertion is: for all $\delta, \delta'$ in the submodule of $\kappa$-linear maps $D \colon \Gamma(X,U) \to \kappa$ with $D(ab) = \mathrm{ev}(a)D(b) + \mathrm{ev}(b)D(a)$, and all ring homomorphisms $\chi, \chi', \chi'' \colon \Gamma(X,U) \to \kappa[\varepsilon]$ into the dual numbers whose first components all equal $\mathrm{ev}$ and whose second components are $\delta$, $\delta'$ and $\delta + \delta'$ respectively, and for all $\kappa[\varepsilon]$-points $P, P'$ of $X$ over the morphism $\operatorname{Spec}\kappa[\varepsilon] \to \operatorname{Spec}\kappa$ induced by $\kappa \to \kappa[\varepsilon]$, if $P$ is $\operatorname{Spec}(\chi)$ followed by the canonical morphism $\operatorname{Spec}\Gamma(X,U) \to X$ attached to the affine open $U$, and $P'$ is likewise given by $\chi'$, then the underlying morphism of $L.\mathrm{mul}$ applied to $P$ and $P'$ is $\operatorname{Spec}(\chi'')$ followed by that same morphism.
--
--   This is the statement that on the tangent space at the unit section, any relative group law induces addition of the corresponding point derivations, in the concrete form of dual-number points factoring through a chosen affine open neighbourhood of the unit. It is used in the identification of the space of tangent vectors at the unit with the module of point derivations, and through that in the analysis of tangent spaces arising in the quaternionic moduli setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_mul_eq_specMap_fromSpec_of_pointDerivations_add.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Scheme.TwoAffineOpenCover

theorem CerednikDrinfeld.QM.mul_eq_specMap_fromSpec_of_pointDerivations_add
    (κ : Type) [Field κ] {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of κ))
    (L : RelativeGroupLaw κ fX)
    (U : X.Opens) (hU : IsAffineOpen U)
    (e₁ : Spec (CommRingCat.of κ) ⟶ (U : Scheme.{0})) (he₁ : e₁ ≫ U.ι = (L.one (𝟙 _)).1) :
    letI := algebraOfHom fX U
    ∀ (δ δ' : ↥(Algebra.PointDerivations κ Γ(X, U) ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) κ)) (χ χ' χ'' : Γ(X, U) →+* DualNumber κ),
      (∀ a : Γ(X, U), TrivSqZeroExt.fst (χ a) = ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) a) →
      (∀ a : Γ(X, U), TrivSqZeroExt.snd (χ a) = (δ : Γ(X, U) →ₗ[κ] κ) a) →
      (∀ a : Γ(X, U), TrivSqZeroExt.fst (χ' a) = ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) a) →
      (∀ a : Γ(X, U), TrivSqZeroExt.snd (χ' a) = (δ' : Γ(X, U) →ₗ[κ] κ) a) →
      (∀ a : Γ(X, U), TrivSqZeroExt.fst (χ'' a) = ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) a) →
      (∀ a : Γ(X, U), TrivSqZeroExt.snd (χ'' a) = (δ : Γ(X, U) →ₗ[κ] κ) a + (δ' : Γ(X, U) →ₗ[κ] κ) a) →
      ∀ (P P' : SchemeHomOver (tangentBase κ (RingHom.id κ)) fX),
        P.1 = Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec →
        P'.1 = Spec.map (CommRingCat.ofHom χ') ≫ hU.fromSpec →
        (L.mul (tangentBase κ (RingHom.id κ)) P P').1 = Spec.map (CommRingCat.ofHom χ'') ≫ hU.fromSpec := by sorry
