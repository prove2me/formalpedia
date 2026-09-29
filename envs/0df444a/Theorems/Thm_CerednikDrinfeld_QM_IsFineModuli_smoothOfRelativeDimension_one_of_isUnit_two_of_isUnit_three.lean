-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_smoothOfRelativeDimension_one_of_isUnit_two_of_isUnit_three
-- name    : CerednikDrinfeld.QM.IsFineModuli.smoothOfRelativeDimension_one_of_isUnit_two_of_isUnit_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/b073045a-ee14-5aba-9b2d-36911b4af061
-- title:
--   Smoothness of relative dimension one for a fine moduli scheme of fake elliptic curves, with 6 invertible
-- statement:
--   Let $q \ne q'$ be primes, and let $a, b \in \mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q}, a, b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $a > 0$ or $b > 0$, and for every height-one prime $v$ of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible precisely when $v$ divides $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $N \ge 1$ and $m \ge 3$ be natural numbers, and let $\mathcal{O}$ be a commutative ring in which the images of $N$, $m$, $qq'$, $2$ and $3$ are units. Let $\pi_M : M \to \operatorname{Spec}\mathcal{O}$ be a morphism of schemes, locally of finite type, together with a rule $\mathrm{ptF}$ assigning to each commutative ring $S$, each $\mathcal{O}$-structure $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and each pair consisting of a fake elliptic curve $E$ over $S$ with $\Lambda$-action and level-$N$ data together with a full level-$m$ structure on $E$, a morphism $\operatorname{Spec} S \to M$ over $s$. Assume `IsFineModuli Λ N m M πM ptF`, that is: $\mathrm{ptF}$ is constant on isomorphism classes, is compatible with pullback of the moduli datum along any ring homomorphism $S \to S'$, is surjective onto the $S$-points of $M$ over $s$ for every $S$ and $s$, and identifies only isomorphic data. Then $\pi_M$ is smooth of relative dimension $1$.
--
--   This is the smoothness statement for the integral model of a Shimura curve attached to an indefinite rational quaternion algebra ramified exactly at $q$ and $q'$, in the form: any fine moduli scheme for fake elliptic curves with level-$N$ and full level-$m$ structure over a base on which $6Nmqq'$ is invertible is smooth of relative dimension one. It is the variant of the finite-type-base result for an arbitrary base ring with $2$ and $3$ invertible, and feeds into the existence statement for such fine moduli schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_smoothOfRelativeDimension_one_of_isUnit_two_of_isUnit_three.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.smoothOfRelativeDimension_one_of_isUnit_two_of_isUnit_three
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (m : ℕ) (hm : 3 ≤ m)
    (𝒪 : Type) [CommRing 𝒪] (hN : IsUnit ((N : ℕ) : 𝒪)) (hm' : IsUnit ((m : ℕ) : 𝒪)) (hqq'u : IsUnit ((q * q' : ℕ) : 𝒪))
    (h2 : IsUnit ((2 : ℕ) : 𝒪)) (h3 : IsUnit ((3 : ℕ) : 𝒪))
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF) (hlft : LocallyOfFiniteType πM) :
    SmoothOfRelativeDimension 1 πM := by sorry
