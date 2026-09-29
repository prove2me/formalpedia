-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuli_finite_etale_of_isUnit
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuli_finite_etale_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/2b5ab78b-f31b-5e35-8bdf-f2e27f0dbd0a
-- title:
--   Level-N fine moduli is finite étale over level 1
-- statement:
--   Let $q\neq q'$ be primes and $a,b\in\mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements units exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order maximal among the orders containing it, let $N\geq 1$ and $m\geq 3$, and let $\mathcal{O}$ be a commutative ring in which the images of $N$ and $m$ are units. Suppose given a scheme $M_1$, a morphism $\pi_1:M_1\to\operatorname{Spec}\mathcal{O}$ and an assignment $\mathrm{ptF}_1$ sending each commutative ring $S$, each morphism $s:\operatorname{Spec}S\to\operatorname{Spec}\mathcal{O}$ and each pair consisting of a fake elliptic curve over $S$ with $\Lambda$-action and level datum $1$ together with a full level-$m$ structure on it (a section $P$ of the structure morphism killed by $m$ for the relative group law, whose $\Lambda$-orbit exhausts the $m$-torsion at every geometric point, and whose annihilator in $\Lambda$ is $m\Lambda$) to a section of $\pi_1$ over $s$, and assume `IsFineModuli Λ 1 m M₁ π₁ ptF₁`: $\mathrm{ptF}_1$ is constant on isomorphism classes, compatible with pullback along ring homomorphisms, surjective onto the sections of $\pi_1$ over each $s$, and injective up to isomorphism. Then there exist a scheme $M$, a morphism $f:M\to M_1$ and an assignment $\mathrm{ptF}$ for objects with level datum $N$ and full level $m$ such that `IsFineModuli Λ N m M (f ≫ π₁) ptF` holds and $f$ is finite and étale. No compatibility of $\mathrm{ptF}$ with $\mathrm{ptF}_1$ under $f$ is asserted.
--
--   This is the relative representability of the passage from level datum $1$ to level datum $N$ on the moduli problem of fake elliptic curves with full level-$m$ structure: the level-$N$ fine moduli scheme is obtained as a finite étale cover of the level-$1$ one, over a base in which $N$ and $m$ are invertible. It feeds the geometric properties of the resulting Shimura-curve model established downstream, namely flatness over $\mathbb{Z}_p$, smoothness of relative dimension one, and the existence statement [`CerednikDrinfeld.QM.exists_isFineModuli_of_isUnit_two_of_isUnit_three`](thm.html#CerednikDrinfeld.QM.exists_isFineModuli_of_isUnit_two_of_isUnit_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuli_finite_etale_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuli_finite_etale_of_isUnit
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (m : ℕ) (hm : 3 ≤ m)
    (𝒪 : Type) [CommRing 𝒪] (hN : IsUnit ((N : ℕ) : 𝒪)) (hm' : IsUnit ((m : ℕ) : 𝒪))
    {M₁ : Scheme.{0}} {π₁ : M₁ ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF₁ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ 1 m S → SchemeHomOver s π₁}
    (hM₁ : IsFineModuli Λ 1 m M₁ π₁ ptF₁) :
    ∃ (M : Scheme.{0}) (f : M ⟶ M₁)
      (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s (f ≫ π₁)),
      IsFineModuli Λ N m M (f ≫ π₁) ptF ∧ IsFinite f ∧ Etale f := by sorry
