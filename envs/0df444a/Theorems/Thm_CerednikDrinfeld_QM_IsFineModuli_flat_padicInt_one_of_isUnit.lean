-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_flat_padicInt_one_of_isUnit
-- name    : CerednikDrinfeld.QM.IsFineModuli.flat_padicInt_one_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/9e4eb0db-4390-5cbc-b555-9d4f464d1f65
-- title:
--   Flatness over ℤ_q of the fine moduli scheme at level (1;m)
-- statement:
--   Let $q \neq q'$ be primes, let $a,b \in \mathbb{Q}$ and suppose the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order and is maximal among orders, and let $m \geq 3$ be an integer whose image in $\mathbb{Z}_q$ is a unit. Let $\pi_M : M \to \operatorname{Spec}\mathbb{Z}_q$ be a morphism of schemes together with a rule $\mathrm{ptF}$ assigning, to each commutative ring $S$, each morphism $s : \operatorname{Spec} S \to \operatorname{Spec}\mathbb{Z}_q$ and each pair consisting of a fake elliptic curve over $S$ with $\Lambda$-action at level $N = 1$ and a full level-$m$ structure on it (a section $P$ of the abelian scheme killed by $m$ whose $\Lambda$-orbit exhausts the $m$-torsion at every geometric point and whose annihilator in $\Lambda$ is $m\Lambda$), a point of $M$ over $s$; assume `IsFineModuli Λ 1 m M πM ptF`, that is, $\mathrm{ptF}$ depends only on the isomorphism class of its argument, is compatible with base change along ring maps and pullback data, and is surjective and injective up to isomorphism on each such set of $S$-points. Then $\pi_M$ is flat.
--
--   This is the level-one case of the integrality (flatness over $\mathbb{Z}_q$) of the Drinfeld integral model of the Shimura curve attached to an indefinite rational quaternion algebra ramified exactly at $q$ and $q'$: no component of the fine moduli scheme is supported in the special fibre. It feeds the flatness statement at general $\Gamma_0$-level, [`CerednikDrinfeld.QM.IsFineModuli.flat_padicInt_of_isUnit_of_isUnit_two_of_isUnit_three`](thm.html#CerednikDrinfeld.QM.IsFineModuli.flat_padicInt_of_isUnit_of_isUnit_two_of_isUnit_three), via a finite étale level cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_flat_padicInt_one_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open AlgebraicGeometry

theorem CerednikDrinfeld.QM.IsFineModuli.flat_padicInt_one_of_isUnit
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q) {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (m : ℕ) (hm : 3 ≤ m)
    (hm' : IsUnit ((m : ℕ) : ℤ_[q]))
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of ℤ_[q])}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of ℤ_[q])),
      FakeEllipticCurve.WithFullLevel Λ 1 m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ 1 m M πM ptF) :
    Flat πM := by sorry
