-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_isProper_of_isUnit_two_of_isUnit_three
-- name    : CerednikDrinfeld.QM.IsFineModuli.isProper_of_isUnit_two_of_isUnit_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/8c80ff8a-b2d9-51ab-b21a-1cedf1c43155
-- title:
--   Properness of the fine moduli scheme of fake elliptic curves
-- statement:
--   Let $q \neq q'$ be primes, let $a,b \in \mathbb{Q}$ and assume `IsIndefiniteRamifiedExactlyAt a b q q'`: $a > 0$ or $b > 0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. an order not properly contained in any order. Let $N \neq 0$ and $m \geq 3$ be natural numbers, and let $\mathcal{O}$ be a characteristic-zero integral domain in which the images of $N$, $m$, $2$ and $3$ are units. Let $M$ be a scheme, $\pi_M : M \to \operatorname{Spec} \mathcal{O}$ a morphism, and $\mathrm{ptF}$ a rule assigning to every commutative ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec} \mathcal{O}$ and every pair consisting of a fake elliptic curve $E$ over $S$ with $\Lambda$-action and $\Gamma_0(N)$-type level datum together with a full level-$m$ structure on $E$ (a section killed by $m$ whose $\Lambda$-orbit exhausts the $m$-torsion at geometric points and whose annihilator in $\Lambda$ is $m\Lambda$), a morphism $\operatorname{Spec} S \to M$ over $s$. Assume `IsFineModuli`: $\mathrm{ptF}$ is constant on isomorphism classes, compatible with pullback along ring homomorphisms, surjective onto morphisms over $s$, and injective up to isomorphism of the moduli data. Then $\pi_M$ is proper.
--
--   This is the properness of the integral fine moduli scheme of fake elliptic curves with $\Lambda$-action and full level-$m$ structure, over an arbitrary characteristic-zero domain base in which $2$, $3$, $N$ and $m$ are invertible; it is the geometric input behind properness and integrality statements for the corresponding coarse moduli schemes (Shimura curves), which cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_isProper_of_isUnit_two_of_isUnit_three.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.isProper_of_isUnit_two_of_isUnit_three
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N m : ℕ) [NeZero N] (hm : 3 ≤ m)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hN : IsUnit ((N : ℕ) : 𝒪)) (hm' : IsUnit ((m : ℕ) : 𝒪))
    (h2 : IsUnit ((2 : ℕ) : 𝒪)) (h3 : IsUnit ((3 : ℕ) : 𝒪))
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF) :
    IsProper πM := by sorry
