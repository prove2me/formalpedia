-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isAtkinLehnerQuotient_comp_of_commRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/fa24dcd1-0b80-508b-9e5d-fc8872d1513b
-- title:
--   Double Atkin–Lehner quotient at a ramified prime returns the pair
-- statement:
--   Let $q\neq q'$ be primes, let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of the integers of $\mathbb{Q}$, the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$, and let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among orders for inclusion. Let $N\neq 0$ with $q\nmid N$ and $q'\nmid N$, let $r$ be $q$ or $q'$, and let $\ell$ be a prime distinct from $q$ and $q'$. Let $S$ be a commutative ring and $u,u',u''$ three fake elliptic curves over $S$ for $(\Lambda,N)$ — an abelian scheme datum $f\colon A\to\operatorname{Spec}S$ with commutative relative group law, two-dimensional fibres, a $\Lambda$-action satisfying the trace condition, and a level-$N$ structure $\mathrm{lev}$ — each equipped with an extra level structure $\mathrm{levK}$ of level $\ell$. Assume $u'$ is an Atkin–Lehner quotient of $u$ at $r$, and $u''$ one of $u'$: that is, in each case there are mutually dual $S$-morphisms $\varphi,\psi$ between the underlying schemes, additive on points and $\Lambda$-equivariant, with $\varphi\psi$ and $\psi\varphi$ the action of $r$ whenever $r\in\Lambda$, with $\varphi$ killing exactly those points annihilated by all $m\in\Lambda$ of reduced norm in $r\mathbb{Z}$, and with $\varphi$ carrying points factoring through $\mathrm{lev}$, resp. $\mathrm{levK}$, to points factoring through the target's $\mathrm{lev}$, resp. $\mathrm{levK}$. Then $u$ and $u''$ are isomorphic: there is an isomorphism of the underlying schemes over $S$ that is additive on points, commutes with the $\Lambda$-actions, and matches the conditions of factoring through $\mathrm{lev}$ and through $\mathrm{levK}$ in both directions.
--
--   This is the statement that the Atkin–Lehner involution at a prime where the quaternion algebra ramifies squares to the identity, in the moduli-theoretic form of fake elliptic curves with auxiliary level structure, over an arbitrary commutative base ring. It feeds, through the uniqueness half of the coarse moduli property, into [`CerednikDrinfeld.QM.exists_WT_of_coarse_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.exists_WT_of_coarse_of_two_mul_dvd), where the corresponding involution of the Shimura curve is produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp_of_commRing.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isAtkinLehnerQuotient_comp_of_commRing
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (r : ℕ) (hr : r = q ∨ r = q') (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (S : Type) [CommRing S] (u u' u'' : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
    (h : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u u')
    (h' : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u' u'') :
    QM.FakeEllipticCurve.WithExtraLevel.Iso u u'' := by sorry
