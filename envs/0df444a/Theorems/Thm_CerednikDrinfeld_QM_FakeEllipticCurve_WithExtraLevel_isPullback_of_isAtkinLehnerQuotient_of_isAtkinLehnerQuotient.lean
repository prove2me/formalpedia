-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isPullback_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.isPullback_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/96611b64-209e-587b-9751-8f168ee1852d
-- title:
--   Atkin–Lehner quotients of pairs commute with base change
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, and let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $a>0$ or $b>0$, and for every finite place $v$ of $\mathbb{Q}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $q$ or $q'$ lies in $v$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is a maximal order (an order maximal among orders containing it), let $N\neq 0$ with $q\nmid N$ and $q'\nmid N$, let $r\in\{q,q'\}$, and let $\ell$ be a prime distinct from $q$ and $q'$. Let $S,S'$ be commutative rings, $\varphi:S\to S'$ a ring homomorphism, $u,u'$ fake elliptic curves over $S$ for $\Lambda$ and $N$ equipped with extra level $\ell$ data, and $v,v'$ such objects over $S'$. Assume `IsPullback φ u v`, i.e. there is $g:v_{1}.A\to u_{1}.A$ making the square formed by $v_1.f$, $u_1.f$ and $\mathrm{Spec}\,\varphi$ cartesian, with $g$ additive on relative $T$-points, commuting with the $\Lambda$-action ($v_1.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $u_1.\mathrm{act}\,x$), and carrying points factoring through $v_1.\mathrm{lev}$, resp. $v_2.\mathrm{levK}$, to points factoring through $u_1.\mathrm{lev}$, resp. $u_2.\mathrm{levK}$. Assume further `IsAtkinLehnerQuotient r u u'` and `IsAtkinLehnerQuotient r v v'`: in each case a pair of mutually dual $S$- (resp. $S'$-) morphisms, additive on points, commuting with $\Lambda$, whose composites are the action of $r$ whenever $r\in\Lambda$, with the prescribed kernel criterion in terms of $m\,\overline{m}=rn$ and preservation of both level structures. Then `IsPullback φ u' v'` holds.
--
--   This is the compatibility of the Atkin–Lehner quotient at $r\in\{q,q'\}$ with base change along $\varphi$ for the moduli problem of fake elliptic curves with extra level $\ell$: a quotient of a base-changed object is the base change of the quotient. It feeds into [`CerednikDrinfeld.QM.exists_WT_of_coarse_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.exists_WT_of_coarse_of_two_mul_dvd), in the Čerednik–Drinfeld description of Shimura curves attached to the indefinite quaternion algebra ramified exactly at $q$ and $q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isPullback_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.isPullback_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (r : ℕ) (hr : r = q ∨ r = q') (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (u u' : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (v v' : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S')
    (hv : QM.FakeEllipticCurve.WithExtraLevel.IsPullback φ u v)
    (h : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u u')
    (h' : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r v v') :
    QM.FakeEllipticCurve.WithExtraLevel.IsPullback φ u' v' := by sorry
