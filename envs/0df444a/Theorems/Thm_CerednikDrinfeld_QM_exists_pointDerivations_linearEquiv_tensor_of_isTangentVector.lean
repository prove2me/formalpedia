-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_pointDerivations_linearEquiv_tensor_of_isTangentVector
-- name    : CerednikDrinfeld.QM.exists_pointDerivations_linearEquiv_tensor_of_isTangentVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/1e3acafa-3719-5a1c-8069-f4d035a0d8b1
-- title:
--   Point derivations at the unit are V⊗_κ M
-- statement:
--   Let $\kappa$ be a field, let $X$ be a scheme with a morphism $f_X : X \to \operatorname{Spec}\kappa$ that is locally of finite type, and let $L$ be a relative group law on $f_X$: a functorial group structure on the sets $\{\varphi : T \to X \mid \varphi \circ t = \text{(structure map)}\}$ of $X$-points over each $t : T \to \operatorname{Spec}\kappa$, with associativity, unit, inverses and compatibility with base change. Let $U \subseteq X$ be an affine open and $e_1 : \operatorname{Spec}\kappa \to U$ a section whose composite with the inclusion $U \hookrightarrow X$ is the unit of $L$ over the identity of $\operatorname{Spec}\kappa$; write $\mathrm{ev} : \Gamma(X,U) \to \kappa$ for the ring map obtained from $e_1$ on global sections (through $U$'s top-open isomorphism and $\Gamma\!\operatorname{Spec}$), and give $\Gamma(X,U)$ the $\kappa$-algebra structure coming from $f_X$. Let $V$ be a $\kappa$-vector space together with a map $\tau$ from $V$ to the morphisms $\operatorname{Spec}\kappa[\varepsilon] \to X$ lying over $\operatorname{Spec}$ of $\kappa \to \kappa[\varepsilon]$, assumed injective, with image exactly those points $P$ with $\operatorname{Spec}(\varepsilon \mapsto 0) \circ P$ equal to the unit point, additive for the multiplication of $L$ over $\operatorname{Spec}\kappa[\varepsilon]$, and homogeneous in the sense $\tau(c \cdot v) = \tau(v) \circ \operatorname{Spec}(\varepsilon \mapsto c\varepsilon)$ for $c \in \kappa$. Then there is a family of $\kappa$-linear isomorphisms $\Phi_M : \mathcal P(M) \to V \otimes_\kappa M$, indexed by $\kappa$-modules $M$, where $\mathcal P(M)$ is the submodule of $\kappa$-linear maps $D : \Gamma(X,U) \to M$ satisfying $D(ab) = \mathrm{ev}(a)\,D(b) + \mathrm{ev}(b)\,D(a)$, such that (i) for every $\kappa$-linear $g : M \to M'$ and every $\delta \in \mathcal P(M)$ one has $\Phi_{M'}(g \circ \delta) = (\mathrm{id}_V \otimes g)(\Phi_M(\delta))$, and (ii) for every $\delta \in \mathcal P(\kappa)$ and every ring homomorphism $\chi : \Gamma(X,U) \to \kappa[\varepsilon]$ whose first coordinate is $\mathrm{ev}$ and whose second coordinate is $\delta$, the $\kappa[\varepsilon]$-point $\tau$ of the image of $\Phi_\kappa(\delta)$ under $V \otimes_\kappa \kappa \cong V$ is $\operatorname{Spec}(\chi)$ followed by the canonical map $\operatorname{Spec}\Gamma(X,U) \to X$ attached to the affine open $U$.
--
--   This identifies the module of $M$-valued point derivations at the unit on an affine chart with $V \otimes_\kappa M$, $V$ being any presentation of the tangent space at the unit by $\kappa[\varepsilon]$-points of the group law; clause (ii) pins the isomorphism down by matching derivations with dual-number points. It is used in the analysis of deformations over dual numbers of fake elliptic curves and of the Jacobians occurring in the Čerednik–Drinfel'd part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_pointDerivations_linearEquiv_tensor_of_isTangentVector.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Scheme.TwoAffineOpenCover

theorem CerednikDrinfeld.QM.exists_pointDerivations_linearEquiv_tensor_of_isTangentVector
    (κ : Type) [Field κ] {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType fX]
    (L : RelativeGroupLaw κ fX)
    (U : X.Opens) (hU : IsAffineOpen U)
    (e₁ : Spec (CommRingCat.of κ) ⟶ (U : Scheme.{0})) (he₁ : e₁ ≫ U.ι = (L.one (𝟙 _)).1)

    (V : Type) [AddCommGroup V] [Module κ V]
    (τ : V → SchemeHomOver (tangentBase κ (RingHom.id κ)) fX)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase κ (RingHom.id κ)) fX, P ∈ Set.range τ ↔ IsTangentVector L κ (RingHom.id κ) P)
    (hadd : ∀ v w : V, τ (v + w) = L.mul (tangentBase κ (RingHom.id κ)) (τ v) (τ w))
    (hsmul : ∀ (c : κ) (v : V), (τ (c • v)).1 = tangentScale κ c ≫ (τ v).1) :
    letI := algebraOfHom fX U
    ∃ Φ : ∀ (M : Type) [AddCommGroup M] [Module κ M],
        ↥(Algebra.PointDerivations κ Γ(X, U) ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) M) ≃ₗ[κ]
          (V ⊗[κ] M),

      (∀ (M M' : Type) [AddCommGroup M] [Module κ M] [AddCommGroup M'] [Module κ M'] (g : M →ₗ[κ] M')
          (δ : ↥(Algebra.PointDerivations κ Γ(X, U) ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) M)),
        Φ M' (Algebra.PointDerivations.map _ g δ) = TensorProduct.map (LinearMap.id : V →ₗ[κ] V) g (Φ M δ)) ∧

      (∀ (δ : ↥(Algebra.PointDerivations κ Γ(X, U) ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) κ))
          (χ : Γ(X, U) →+* DualNumber κ),
        (∀ a : Γ(X, U), TrivSqZeroExt.fst (χ a) = ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) a) →
        (∀ a : Γ(X, U), TrivSqZeroExt.snd (χ a) = (δ : Γ(X, U) →ₗ[κ] κ) a) →
        (τ (TensorProduct.rid κ V (Φ κ δ))).1 = Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec) := by sorry
