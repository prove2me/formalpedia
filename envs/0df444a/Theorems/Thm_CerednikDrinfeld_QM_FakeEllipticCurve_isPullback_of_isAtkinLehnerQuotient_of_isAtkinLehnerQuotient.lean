-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isPullback_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isPullback_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/fbd895c3-5c7e-5183-a1f6-40031a49a10a
-- title:
--   Atkin–Lehner quotients commute with base change
-- statement:
--   Fix primes $q \neq q'$, rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $N$ be a nonzero level prime to $q$ and to $q'$, and let $r$ be $q$ or $q'$. Given commutative rings $S, S'$, a ring homomorphism $\varphi : S \to S'$, fake elliptic curves $E, E'$ of level $N$ for $\Lambda$ over $S$ and $F, F'$ over $S'$, assume: $F$ is a base change of $E$ along $\varphi$, in the sense that there is $g : F.A \to E.A$ exhibiting $F.f$ as the pullback of $E.f$ along $\mathrm{Spec}\,\varphi$, compatible with the relative group laws, commuting with the $\Lambda$-actions, and carrying points that factor through the level cover of $F$ to points factoring through that of $E$; and that both $E'$ and $F'$ are Atkin–Lehner quotients at $r$ of $E$ and of $F$ respectively, meaning there are mutually dual morphisms over the base in both directions, additive for the group laws, commuting with the $\Lambda$-actions, whose composites are the action of the scalar $r$ when $r \in \Lambda$, whose kernel is described by annihilation under all $m \in \Lambda$ with $m \bar m = rn$ for some $n \in \mathbb{Z}$, and which preserve level structures. Then $F'$ is a base change of $E'$ along $\varphi$ in the same sense.
--
--   This is the compatibility of the Atkin–Lehner quotient at $r \in \{q,q'\}$ with base change along a ring homomorphism, in the setting of fake elliptic curves for a maximal order in an indefinite quaternion algebra ramified exactly at $q$ and $q'$. It feeds the construction of the Atkin–Lehner involution on the coarse moduli space, via [`CerednikDrinfeld.QM.IsCoarseModuli.exists_atkinLehner_involution`](thm.html#CerednikDrinfeld.QM.IsCoarseModuli.exists_atkinLehner_involution) and its variant for invertible $r$; the proof cites the existence of base changes, the base-change invariance of the Atkin–Lehner quotient relation, and the uniqueness of that quotient up to isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isPullback_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isPullback_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (r : ℕ) (hr : r = q ∨ r = q')
    (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (E E' : QM.FakeEllipticCurve Λ N S) (F F' : QM.FakeEllipticCurve Λ N S')
    (hF : QM.FakeEllipticCurve.IsPullback φ E F) (h : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E E')
    (h' : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r F F') :
    QM.FakeEllipticCurve.IsPullback φ E' F' := by sorry
