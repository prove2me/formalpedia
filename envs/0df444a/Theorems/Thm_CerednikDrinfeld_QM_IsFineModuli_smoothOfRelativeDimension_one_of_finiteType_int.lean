-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_smoothOfRelativeDimension_one_of_finiteType_int
-- name    : CerednikDrinfeld.QM.IsFineModuli.smoothOfRelativeDimension_one_of_finiteType_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/62be5d1d-8dab-50da-9a25-15bf252f0823
-- title:
--   Smoothness of relative dimension one for a fine moduli scheme
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, its completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra (every nonzero element is a unit) precisely when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders for inclusion, let $N$ be a nonzero natural number and $m\geq 3$. Let $\mathcal{O}$ be a commutative ring of finite type over $\mathbb{Z}$ in which the images of $N$, $m$ and $qq'$ are units. Let $\pi_M\colon M\to\operatorname{Spec}\mathcal{O}$ be a morphism of schemes, and let $\mathrm{ptF}$ assign, to every commutative ring $S$, every $s\colon\operatorname{Spec}S\to\operatorname{Spec}\mathcal{O}$ and every pair consisting of a fake elliptic curve over $S$ with $\Lambda$-action and $N$-level datum together with a full level-$m$ structure on it (a section that is $m$-torsion, whose $\Lambda$-orbit exhausts the geometric $m$-torsion, and whose annihilator in $\Lambda$ is $m\Lambda$), a morphism $\operatorname{Spec}S\to M$ whose composite with $\pi_M$ is $s$. Assume $(M,\pi_M,\mathrm{ptF})$ is a fine moduli scheme for this data, that is: $\mathrm{ptF}$ takes isomorphic objects to the same morphism, is compatible with pullback along ring maps $\varphi\colon S\to S'$ over $\operatorname{Spec}\mathcal{O}$, and for each $S$ and $s$ induces a surjection onto the morphisms $\operatorname{Spec}S\to M$ over $s$ whose fibres consist of isomorphic objects. Assume further that $\pi_M$ is locally of finite type. Then $\pi_M$ is smooth of relative dimension $1$.
--
--   This is the smoothness statement for an integral model of the Shimura curve attached to an indefinite quaternion algebra ramified exactly at $q$ and $q'$, with auxiliary level $N$ and full level $m$, over a base where $N$, $m$ and $qq'$ are invertible; it is phrased as a hypothesis on `IsFineModuli` so that it applies to any scheme representing the moduli problem. It feeds the variant formulated with $2$ and $3$ invertible, [`CerednikDrinfeld.QM.IsFineModuli.smoothOfRelativeDimension_one_of_isUnit_two_of_isUnit_three`](thm.html#CerednikDrinfeld.QM.IsFineModuli.smoothOfRelativeDimension_one_of_isUnit_two_of_isUnit_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_smoothOfRelativeDimension_one_of_finiteType_int.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.smoothOfRelativeDimension_one_of_finiteType_int
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (m : ℕ) (hm : 3 ≤ m)
    (𝒪 : Type) [CommRing 𝒪] [Algebra.FiniteType ℤ 𝒪] (hN : IsUnit ((N : ℕ) : 𝒪)) (hm' : IsUnit ((m : ℕ) : 𝒪)) (hqq'u : IsUnit ((q * q' : ℕ) : 𝒪))
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF) (hlft : LocallyOfFiniteType πM) :
    SmoothOfRelativeDimension 1 πM := by sorry
