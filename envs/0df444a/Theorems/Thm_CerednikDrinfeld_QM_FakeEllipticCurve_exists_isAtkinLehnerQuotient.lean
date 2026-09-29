-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotient
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isAtkinLehnerQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/bedd878e-145f-568b-99a8-28420bf8dddc
-- title:
--   Existence of Atkin–Lehner quotients of fake elliptic curves
-- statement:
--   Let $q\neq q'$ be primes and $a,b\in\mathbb Q$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, that is: $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb Q$, every nonzero element of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb Z$-submodule of $\mathbb H[\mathbb Q,a,b]$ which is a maximal order (an order, and the only order containing it is itself), let $N\neq 0$ be a natural number divisible by neither $q$ nor $q'$, and let $r$ be $q$ or $q'$. Then for every commutative ring $S$ and every $E$ of type `QM.FakeEllipticCurve Λ N S` — a scheme $A$ over $\operatorname{Spec}S$ carrying a commutative relative group law, the abelian-scheme property bundle (smooth, proper, connected fibres, group law present), fibres of Krull dimension $2$, an action of $\Lambda$ by endomorphisms over $\operatorname{Spec}S$ that are group-law homomorphisms, additive in $\Lambda$, anti-multiplicative ($\operatorname{act}(xy)=\operatorname{act}y$ followed by $\operatorname{act}x$), unital, with trace of the induced map on tangent spaces equal to the reduced trace, together with the level-$N$ data $C$, $\mathrm{lev}$ and the accompanying axioms — there exists $E'$ of the same type with `QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E E'`: morphisms $\varphi\colon E.A\to E'.A$ and $\psi\colon E'.A\to E.A$ over $\operatorname{Spec}S$, each compatible with the group laws on $T$-points and commuting with the $\Lambda$-actions, such that whenever the image of $r$ lies in $\Lambda$ one has $\psi\circ\varphi=\operatorname{act}r$ on $E$ and $\varphi\circ\psi=\operatorname{act}r$ on $E'$; moreover a $T$-point $P$ of $E$ has $\varphi(P)$ equal to the identity section precisely when $\operatorname{act}m$ kills $P$ for every $m\in\Lambda$ whose reduced norm $m\,\overline m$ is an integer multiple of $r$, and $\varphi$ carries points factoring through $E.\mathrm{lev}$ to points factoring through $E'.\mathrm{lev}$.
--
--   This is the existence half of the Atkin–Lehner construction at a prime where the quaternion algebra ramifies: the quotient of a fake elliptic curve by the kernel of the two-sided ideal above $r$, with its induced $\Lambda$-action and level-$N$ structure, presented purely as a moduli-theoretic statement over an arbitrary base ring. It feeds the variant with $r$ invertible and, via the coarse moduli interpretation, the construction of the Atkin–Lehner involution on the associated Shimura curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotient.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isAtkinLehnerQuotient
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (r : ℕ) (hr : r = q ∨ r = q')
    (S : Type) [CommRing S] (E : QM.FakeEllipticCurve Λ N S) :
    ∃ E' : QM.FakeEllipticCurve Λ N S, QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E E' := by sorry
