-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_class_bareDeformation_dualNumber_forall_isIso_iff_of_isAlgClosed_of_charP
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_class_bareDeformation_dualNumber_forall_isIso_iff_of_isAlgClosed_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/731503d0-5d4a-5e7b-a046-5ec113040318
-- title:
--   First-order deformations of a fake elliptic curve over k[ε]
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and $N\in\mathbb{N}$; let $k$ be an algebraically closed field of characteristic a prime $\ell$, and let $E$ be a fake elliptic curve of level data $(\Lambda,N)$ over $k$, i.e. a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec} k$, a commutative relative group law $E.L$, an abelian-scheme property bundle, two-dimensional fibres, and an action $E.act$ of $\Lambda$ by endomorphisms over $\operatorname{Spec} k$ together with the usual level structures. Let $V$ be a finite-dimensional $k$-vector space and $\tau$ a map from $V$ to sections of $E.f$ over the dual-number base point $\operatorname{Spec} k[\varepsilon]\to\operatorname{Spec} k$, assumed injective, with image exactly the tangent vectors (those sections whose restriction along $\varepsilon\mapsto 0$ is the identity section of $E.L$), additive for $E.L$, and $k$-homogeneous for the scalings $\varepsilon\mapsto c\varepsilon$. Regard $k$ as an algebra over $\mathrm{DualNumber}\,k=k[\varepsilon]$ via the first projection. Then there exist a $k$-vector space $H_1$ with $\dim_k H_1=2$, maps $\rho:\Lambda\to\operatorname{End}_k H_1$ and $\theta:\Lambda\to\operatorname{End}_k V$, and a map $\mathrm{cls}$ from bare deformations of $(E.f,E.L)$ to $k[\varepsilon]$ — abelian-scheme data $D$ over $k[\varepsilon]$ with a morphism $D.g$ from $E.A$ that is cartesian over $\varepsilon\mapsto0$ and compatible with the group laws — to $V\otimes_k H_1$, such that: $\rho$ sends $1$ (when $1\in\Lambda$) to the identity, is additive, and is anti-multiplicative on products lying in $\Lambda$; $\theta$ is the differential of the action, $\tau(\theta(x)v)=E.act(x)\circ\tau(v)$; $\mathrm{cls}$ is surjective; $\mathrm{cls}\,D=\mathrm{cls}\,D'$ if and only if $D$ and $D'$ are isomorphic as bare deformations (an isomorphism of the total spaces over $\operatorname{Spec} k[\varepsilon]$ commuting with the $D.g$); if $h:D'.A\to D.A$ makes $D'$ the pullback of $D$ along $\varepsilon\mapsto c\varepsilon$ with $D'.g$ followed by $h$ equal to $D.g$, then $\mathrm{cls}\,D'=c\,\mathrm{cls}\,D$; if $D$ admits, for each $x\in\Lambda$, an endomorphism of $D.A$ over $\operatorname{Spec} k[\varepsilon]$ intertwining $E.act(x)$ through $D.g$, then $\mathrm{cls}\,D$ satisfies $(\theta(x)\otimes 1)(\mathrm{cls}\,D)=(1\otimes\rho(x))(\mathrm{cls}\,D)$ for all $x$; and conversely every $\xi\in V\otimes_k H_1$ satisfying these equations equals $\mathrm{cls}\,D$ for some bare deformation $D$ with $D.f$ smooth of relative dimension $2$ carrying maps $act:\Lambda\to\operatorname{End}(D.A)$ over $\operatorname{Spec} k[\varepsilon]$ that are homomorphisms for $D.L$, unital, anti-multiplicative and additive in the same sense as for $E$, and compatible with $E.act$ through $D.g$.
--
--   This is the Kodaira–Spencer package for first-order deformations of the abelian surface underlying a fake elliptic curve over an algebraically closed field of positive characteristic: a two-dimensional space $H_1$ playing the role of $\check H^1(A,\mathcal O_A)$ with the contravariant $\Lambda$-action, and a bijective classification of bare deformations over $k[\varepsilon]$ up to isomorphism by $V\otimes_k H_1$, linear in the scaling of $\varepsilon$, with the quaternionically equivariant deformations cut out by the tensor equations. It feeds the statements on pullback along the first projection of the dual numbers used for fake elliptic curves with full level structure and at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_class_bareDeformation_dualNumber_forall_isIso_iff_of_isAlgClosed_of_charP.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_class_bareDeformation_dualNumber_forall_isIso_iff_of_isAlgClosed_of_charP
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (E : FakeEllipticCurve Λ N k)

    (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (τ : V → SchemeHomOver (tangentBase k (RingHom.id k)) E.f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase k (RingHom.id k)) E.f, P ∈ Set.range τ ↔ IsTangentVector E.L k (RingHom.id k) P)
    (hadd : ∀ v w : V, τ (v + w) = E.L.mul (tangentBase k (RingHom.id k)) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) :
    letI : Algebra (DualNumber k) k := (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra
    ∃ (H₁ : Type) (_ : AddCommGroup H₁) (_ : Module k H₁) (_ : Module.Finite k H₁) (_ : Module.finrank k H₁ = 2)
      (ρ : ↥Λ → Module.End k H₁) (θ : ↥Λ → Module.End k V)
      (cls : BareDeformation E.f E.L (DualNumber k) → V ⊗[k] H₁),

      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = 1) ∧
      (∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ρ y * ρ x) ∧

      (∀ (x : ↥Λ) (v : V), τ (θ x v) = pushPt (E.act x) (E.act_over x) (τ v)) ∧

      Function.Surjective cls ∧

      (∀ D D' : BareDeformation E.f E.L (DualNumber k), cls D = cls D' ↔ D.IsIso D') ∧

      (∀ (c : k) (D D' : BareDeformation E.f E.L (DualNumber k)) (h : D'.A ⟶ D.A),
        CategoryTheory.IsPullback h D'.f D.f
          (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom)) →
        D'.g ≫ h = D.g → cls D' = c • cls D) ∧

      (∀ D : BareDeformation E.f E.L (DualNumber k),
        (∀ x : ↥Λ, ∃ φ : D.A ⟶ D.A, φ ≫ D.f = D.f ∧ E.act x ≫ D.g = D.g ≫ φ) →
        ∀ x : ↥Λ, TensorProduct.map (θ x) (LinearMap.id : H₁ →ₗ[k] H₁) (cls D) =
          TensorProduct.map (LinearMap.id : V →ₗ[k] V) (ρ x) (cls D)) ∧

      (∀ ξ : V ⊗[k] H₁,
        (∀ x : ↥Λ, TensorProduct.map (θ x) (LinearMap.id : H₁ →ₗ[k] H₁) ξ =
          TensorProduct.map (LinearMap.id : V →ₗ[k] V) (ρ x) ξ) →
        ∃ (D : BareDeformation E.f E.L (DualNumber k)) (_ : SmoothOfRelativeDimension 2 D.f)
          (act : ↥Λ → (D.A ⟶ D.A)) (act_over : ∀ x : ↥Λ, act x ≫ D.f = D.f),
          ((∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P Q : SchemeHomOver t D.f),
              pushPt (act x) (act_over x) (D.L.mul t P Q) =
                D.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)) ∧
            (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 D.A) ∧
            (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
              act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
            (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P : SchemeHomOver t D.f),
              pushPt (act (x + y)) (act_over (x + y)) P =
                D.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))) ∧
          (∀ x : ↥Λ, E.act x ≫ D.g = D.g ≫ act x) ∧
          cls D = ξ) := by sorry
