-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotient_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isAtkinLehnerQuotient_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/7e3319c3-c8f5-5877-9b53-c47e5f6df739
-- title:
--   Atkin–Lehner quotients of fake elliptic curves over r-invertible bases
-- statement:
--   Fix distinct primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is a maximal order (an order maximal for inclusion among orders), let $N \neq 0$ be a natural number divisible by neither $q$ nor $q'$, and let $r$ be a natural number with $r = q$ or $r = q'$. Let $S$ be a commutative ring in which the image of $r$ is a unit, and let $E$ be a fake elliptic curve of level $N$ for $\Lambda$ over $S$: a scheme $A$ with a structure morphism $f : A \to \operatorname{Spec} S$, a commutative relative group law on $T$-points, the property bundle asserting $f$ smooth and proper with connected fibres, all fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over $S$ which are homomorphisms for the group law, unital, anti-multiplicative and additive in the acting element, satisfying Drinfeld's trace condition on tangent spaces at geometric points, together with the level-$N$ datum $C$ and $\operatorname{lev}$. The conclusion is that some fake elliptic curve $E'$ of level $N$ for $\Lambda$ over $S$ is an Atkin–Lehner quotient of $E$ at $r$: there are morphisms $\varphi : E.A \to E'.A$ and $\psi : E'.A \to E.A$ over $\operatorname{Spec} S$, both additive on $T$-points and commuting with the $\Lambda$-actions, such that whenever $r \in \Lambda$ the composites $\psi \circ \varphi$ and $\varphi \circ \psi$ are the actions of $r$ on $E$ and on $E'$; a $T$-point $P$ of $E$ has $\varphi(P)$ equal to the identity section precisely when $P$ is annihilated by every $m \in \Lambda$ with $m \, \bar{m} = rn$ for some integer $n$; and $\varphi$ sends points factoring through $E.\operatorname{lev}$ to points factoring through $E'.\operatorname{lev}$.
--
--   This is the existence of the quotient $E/E[\mathfrak{P}_r]$ of a fake elliptic curve by the kernel of the ramified prime $\mathfrak{P}_r$ of the maximal order, in the version whose base ring is assumed to invert $r$. It feeds the construction of the Atkin–Lehner involution on the coarse moduli space, [`CerednikDrinfeld.QM.IsCoarseModuli.exists_atkinLehner_involution_of_isUnit`](thm.html#CerednikDrinfeld.QM.IsCoarseModuli.exists_atkinLehner_involution_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotient_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isAtkinLehnerQuotient_of_isUnit
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (r : ℕ) (hr : r = q ∨ r = q')
    (S : Type) [CommRing S] (hrS : IsUnit ((r : ℕ) : S)) (E : QM.FakeEllipticCurve Λ N S) :
    ∃ E' : QM.FakeEllipticCurve Λ N S, QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E E' := by sorry
