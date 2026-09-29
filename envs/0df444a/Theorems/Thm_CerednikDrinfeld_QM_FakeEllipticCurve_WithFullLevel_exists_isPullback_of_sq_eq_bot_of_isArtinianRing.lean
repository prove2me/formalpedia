-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_of_sq_eq_bot_of_isArtinianRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_of_sq_eq_bot_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/a3d261b6-2a4f-59c5-9c27-e884ef463809
-- title:
--   Square-zero lifting of fake elliptic curves with full level
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$ and let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order and is maximal among orders, let $N\geq 1$ and $m\in\mathbb{N}$ with $3\leq m$. Let $S$ be a commutative local Artinian ring whose residue field is algebraically closed of characteristic $\ell$ for a prime $\ell$, let $S_0$ be a commutative ring and $p:S\to S_0$ a surjective ring homomorphism whose kernel satisfies $(\ker p)^2=\bot$, and assume $N$, $m$ and $qq'$ are units in $S$. Then every $u_0$ consisting of a fake elliptic curve over $S_0$ with $\Lambda$-action and level-$N$ structure together with a full level-$m$ structure on it lifts to $S$: there is such a datum $u$ over $S$ and a morphism $g$ from the total space of $u_0$ to that of $u$ making the square over $\operatorname{Spec}$ of $p$ a pullback, compatible with the relative group laws, intertwining the $\Lambda$-actions, carrying points factoring through the level-$N$ structure of $u_0$ into the level structure of $u$, and matching the distinguished $m$-torsion sections.
--
--   This is the infinitesimal (square-zero) lifting property for the moduli problem of fake elliptic curves with $\Lambda$-action, level-$N$ and full level-$m$ structure, over Artinian local bases of positive residue characteristic prime to $Nmqq'$, in the tradition of Serre–Tate local moduli. It feeds the formal-smoothness criterion used in [`CerednikDrinfeld.QM.IsFineModuli.smoothOfRelativeDimension_one_of_finiteType_int`](thm.html#CerednikDrinfeld.QM.IsFineModuli.smoothOfRelativeDimension_one_of_finiteType_int) to establish smoothness of the fine moduli scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_of_sq_eq_bot_of_isArtinianRing.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_of_sq_eq_bot_of_isArtinianRing
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (m : ℕ) (hm : 3 ≤ m)
    (S S₀ : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP (IsLocalRing.ResidueField S) ℓ]
    [CommRing S₀] (p : S →+* S₀) (hp : Function.Surjective p)
    (hI : RingHom.ker p * RingHom.ker p = ⊥)
    (hN : IsUnit ((N : ℕ) : S)) (hm' : IsUnit ((m : ℕ) : S)) (hqq'u : IsUnit ((q * q' : ℕ) : S))
    (u₀ : FakeEllipticCurve.WithFullLevel Λ N m S₀) :
    ∃ u : FakeEllipticCurve.WithFullLevel Λ N m S, FakeEllipticCurve.WithFullLevel.IsPullback p u u₀ := by sorry
