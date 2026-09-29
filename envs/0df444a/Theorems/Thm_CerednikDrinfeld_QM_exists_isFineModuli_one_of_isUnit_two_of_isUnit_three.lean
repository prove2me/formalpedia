-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_isFineModuli_one_of_isUnit_two_of_isUnit_three
-- name    : CerednikDrinfeld.QM.exists_isFineModuli_one_of_isUnit_two_of_isUnit_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/3ddab42d-bb6c-58a6-a8b4-2fae0f24624f
-- title:
--   Fine moduli of fake elliptic curves with full level m
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, let $a,b\in\mathbb{Q}$, and assume `IsIndefiniteRamifiedExactlyAt a b q q'`: that $0<a$ or $0<b$, and that for a height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible exactly when $q\in v$ or $q'\in v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order maximal among orders for inclusion, let $m\geq 3$, and let $\mathcal{O}$ be a commutative ring in which the images of $m$, $2$ and $3$ are units. Then there are a scheme $M_1$, a morphism $\pi_1 : M_1 \to \operatorname{Spec}\mathcal{O}$, and an assignment $\mathrm{ptF}_1$ sending each commutative ring $S$, each $s:\operatorname{Spec} S\to\operatorname{Spec}\mathcal{O}$ and each pair consisting of a fake elliptic curve over $S$ for $\Lambda$ with level parameter $N=1$ together with a full level-$m$ structure on it (a section $P$ of the abelian surface killed by $m$ whose $\Lambda$-orbit exhausts the $m$-torsion at every geometric point and whose annihilator in $\Lambda$ is $m\Lambda$) to a morphism $\operatorname{Spec} S\to M_1$ over $s$, such that: $\mathrm{ptF}_1$ is constant on isomorphism classes, is compatible with pullback along ring homomorphisms, is surjective onto morphisms over $s$, and identifies only isomorphic objects, i.e. `IsFineModuli Λ 1 m M₁ π₁ ptF₁` holds; moreover $\pi_1$ is separated, quasi-compact and locally of finite presentation, and every finite subset of $M_1$ lies in a single affine open.
--
--   This provides the integral fine moduli scheme for fake elliptic curves with full level-$m$ structure and trivial $\Gamma_0$-level over any base in which $6m$ is invertible, the geometric input for the Čerednik–Drinfeld side of the construction of Shimura curves attached to an indefinite quaternion algebra ramified exactly at $q$ and $q'$. It is used for the smoothness of relative dimension one of such fine moduli, for the existence statement without the full-level normalisation, and for producing geometric points over an algebraic closure of $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_isFineModuli_one_of_isUnit_two_of_isUnit_three.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.exists_isFineModuli_one_of_isUnit_two_of_isUnit_three
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (m : ℕ) (hm : 3 ≤ m)
    (𝒪 : Type) [CommRing 𝒪] (hm' : IsUnit ((m : ℕ) : 𝒪))
    (h2 : IsUnit ((2 : ℕ) : 𝒪)) (h3 : IsUnit ((3 : ℕ) : 𝒪))
    :
    ∃ (M₁ : Scheme.{0}) (π₁ : M₁ ⟶ Spec (CommRingCat.of 𝒪))
      (ptF₁ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        FakeEllipticCurve.WithFullLevel Λ 1 m S → SchemeHomOver s π₁),
      IsFineModuli Λ 1 m M₁ π₁ ptF₁ ∧
      IsSeparated π₁ ∧ QuasiCompact π₁ ∧ LocallyOfFinitePresentation π₁ ∧
      (∀ F : Finset M₁, ∃ U : M₁.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) := by sorry
