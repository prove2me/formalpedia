-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_bareDeformation_act_of_ker_mul_ker_eq_bot_of_isArtinianRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_bareDeformation_act_of_ker_mul_ker_eq_bot_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/de276016-c3d8-5d1d-9b04-73d46363ae09
-- title:
--   Λ-equivariant lifting of fake elliptic curves along square-zero thickenings
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is an order maximal among orders containing it, and $N$ a natural number. Let $S$ be an Artinian local ring with algebraically closed residue field of characteristic a prime $\ell$, let $S_0$ be an $S$-algebra with $S \to S_0$ surjective and with kernel $I$ satisfying $I \cdot I = 0$, and assume $qq'$ is a unit in $S$. Then for every fake elliptic curve $E_0$ over $S_0$ (an abelian surface with commutative relative group law, property bundle, two-dimensional fibres, a $\Lambda$-action and level data) there exist a bare deformation $D$ of $(E_0.f, E_0.L)$ over $S$ — a scheme $D.A$ over $\operatorname{Spec} S$ with commutative relative group law $D.L$, abelian scheme property bundle, and a morphism $D.g$ making $E_0.f$ the pullback of $D.f$ along $\operatorname{Spec}(S \to S_0)$ compatibly with the group laws — with $D.f$ smooth of relative dimension $2$, and endomorphisms $\mathrm{act}\,x$ of $D.A$ over $\operatorname{Spec} S$ for $x \in \Lambda$ such that each $\mathrm{act}\,x$ is a homomorphism for $D.L$ on $T$-points for every $T \to \operatorname{Spec} S$, $\mathrm{act}\,1$ is the identity whenever $1 \in \Lambda$, $\mathrm{act}(xy)$ equals $\mathrm{act}\,y$ followed by $\mathrm{act}\,x$, pushforward of a point along $\mathrm{act}(x+y)$ is the $D.L$-product of its pushforwards along $\mathrm{act}\,x$ and $\mathrm{act}\,y$, and $E_0.\mathrm{act}\,x$ followed by $D.g$ equals $D.g$ followed by $\mathrm{act}\,x$ for all $x \in \Lambda$.
--
--   This is the infinitesimal lifting step in the deformation theory of fake elliptic curves: a quaternionic abelian surface over $S_0$ together with its $\Lambda$-action lifts across a square-zero extension $S \to S_0$, provided the residue characteristic is invertible on the quaternionic discriminant $qq'$. It feeds the construction of pullback families with full level structure and the corresponding statements for extra level data in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_bareDeformation_act_of_ker_mul_ker_eq_bot_of_isArtinianRing.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_bareDeformation_act_of_ker_mul_ker_eq_bot_of_isArtinianRing
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ)
    (S S₀ : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP (IsLocalRing.ResidueField S) ℓ]
    [CommRing S₀] [Algebra S S₀]
    (hπ : Function.Surjective (algebraMap S S₀))
    (hI : RingHom.ker (algebraMap S S₀) * RingHom.ker (algebraMap S S₀) = ⊥)
    (hqq'u : IsUnit ((q * q' : ℕ) : S))
    (E₀ : FakeEllipticCurve Λ N S₀) :
    ∃ (D : BareDeformation E₀.f E₀.L S) (_ : SmoothOfRelativeDimension 2 D.f)
      (act : ↥Λ → (D.A ⟶ D.A)) (act_over : ∀ x : ↥Λ, act x ≫ D.f = D.f),
      (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t D.f),
        pushPt (act x) (act_over x) (D.L.mul t P Q) =
          D.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 D.A) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t D.f),
        pushPt (act (x + y)) (act_over (x + y)) P =
          D.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P)) ∧
      (∀ x : ↥Λ, E₀.act x ≫ D.g = D.g ≫ act x) := by sorry
