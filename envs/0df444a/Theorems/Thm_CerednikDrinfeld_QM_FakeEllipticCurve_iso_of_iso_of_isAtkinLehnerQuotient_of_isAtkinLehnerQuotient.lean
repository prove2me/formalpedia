-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/c3adc48f-f696-5df7-8e92-40aee4c730f7
-- title:
--   Atkin–Lehner quotients are unique up to isomorphism
-- statement:
--   Let $q\neq q'$ be primes and $a,b\in\mathbb{Q}$ with `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a>0$ or $b>0$, and for every finite place $v$ of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ lies over $q$ or over $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is a maximal order (an order, maximal among orders containing it), let $N\neq 0$ be a natural number divisible by neither $q$ nor $q'$, and let $r$ be $q$ or $q'$. Let $S$ be a commutative ring and $E,E_1,E',E_1'$ fake elliptic curves over $S$ of level data $(\Lambda,N)$, i.e. abelian schemes of relative dimension $2$ over $\operatorname{Spec} S$ with a commutative relative group law, an action of $\Lambda$ by endomorphisms over $S$ that is additive, multiplicative (anti-)compatibly, trace-normalised by reduced traces, and a level structure morphism `lev`. Assume `Iso E E₁`: there is an isomorphism $E.A\cong E_1.A$ over $\operatorname{Spec} S$ compatible with the group laws on $T$-points, commuting with the $\Lambda$-actions, and matching level structures (a $T$-point factors through $E.\mathrm{lev}$ iff its image factors through $E_1.\mathrm{lev}$). Assume further `IsAtkinLehnerQuotient r E E'` and `IsAtkinLehnerQuotient r E₁ E₁'`: in each case there are morphisms $\varphi$ and $\psi$ over $\operatorname{Spec} S$ between the two abelian schemes, both additive on $T$-points and $\Lambda$-equivariant, with $\psi\circ\varphi$ and $\varphi\circ\psi$ equal to the actions of the scalar $r$ on the source and target whenever $r\in\Lambda$, such that a $T$-point $P$ is killed by $\varphi$ exactly when it is killed by every $m\in\Lambda$ with $m\bar m=rn$ for some $n\in\mathbb{Z}$, and such that $\varphi$ carries points factoring through the level structure to points factoring through the level structure of the target. The conclusion is `Iso E' E₁'`.
--
--   This is the isomorphism-invariance and uniqueness statement for Atkin–Lehner quotients of fake elliptic curves at a prime $r$ of ramification of the quaternion algebra: the quotient is determined, up to isomorphism of fake elliptic curves, by the source up to isomorphism. It is used in constructing the Atkin–Lehner involution on the coarse moduli space, and in the pullback (cartesian square) statement for two Atkin–Lehner quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (r : ℕ) (hr : r = q ∨ r = q')
    (S : Type) [CommRing S] (E E₁ E' E₁' : QM.FakeEllipticCurve Λ N S)
    (hE : QM.FakeEllipticCurve.Iso E E₁) (h : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E E')
    (h₁ : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E₁ E₁') :
    QM.FakeEllipticCurve.Iso E' E₁' := by sorry
