-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_isLevelIsogeny_of_isLevelIsogeny
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_isLevelIsogeny_of_isLevelIsogeny
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/b76e2da0-3a5a-5c82-974d-29911b4b4642
-- title:
--   Atkin–Lehner quotient at r commutes with the ℓ-isogeny leg
-- statement:
--   Fix natural numbers $N\ge 1$ and primes $q,q'$ with $q'\neq q$, neither dividing $N$, and rationals $a,b$ such that the quaternion algebra $B=\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule that is an order and is maximal among the orders containing it, let $\ell$ be a prime distinct from $q$ and $q'$, and let $r$ be $q$ or $q'$. Over $k=\overline{\mathbb{Q}}$, let $u,u'$ be pairs consisting of a fake elliptic curve of level $N$ with $\Lambda$-action together with an extra level structure at $\ell$, and let $d,d'$ be fake elliptic curves of level $N$. Assume: (i) `IsLevelIsogeny ℓ u d`, i.e. there are morphisms $\varphi:u_1.A\to d.A$ and $\psi:d.A\to u_1.A$ over $\operatorname{Spec}k$, additive on $T$-points for every test scheme $T$, commuting with the $\Lambda$-actions, with $\varphi\circ\psi$ and $\psi\circ\varphi$ the action of the scalar $\ell$ whenever $\ell\in\Lambda$, such that a $T$-point is killed by $\varphi$ exactly when it factors through the extra level subscheme `u.2.levK`, and $\varphi$ carries points factoring through `u.1.lev` to points factoring through `d.lev`; (ii) `WithExtraLevel.IsAtkinLehnerQuotient r u u'`, the analogous data between $u$ and $u'$ with composites the action of $r$, with kernel on $T$-points described by the condition that the point be annihilated by every $m\in\Lambda$ with $m\,\overline{m}=rn$ for some $n\in\mathbb{Z}$, and preserving both the level-$N$ and the extra level-$\ell$ factorisations; (iii) `IsLevelIsogeny ℓ u' d'`. Then `IsAtkinLehnerQuotient r d d'` holds: there is a pair of mutually $r$-dual, additive, $\Lambda$-equivariant morphisms between $d$ and $d'$ over $\operatorname{Spec}k$ whose kernel on $T$-points consists of the points annihilated by all $m\in\Lambda$ of reduced norm divisible by $r$ in the above sense, and which preserves level-$N$ structures.
--
--   This is the compatibility, in the moduli tower of fake elliptic curves attached to an indefinite quaternion algebra ramified exactly at $q$ and $q'$, of the Atkin–Lehner involution at a ramified prime $r\in\{q,q'\}$ with the degeneracy leg $(E,K)\mapsto E/K$ given by quotienting by an extra level structure at $\ell$: both composites realise $E/(E[\mathfrak P_r]+K)$. It is used in assembling the tower laws for the Čerednik–Drinfeld moduli data ([`CerednikDrinfeld.QM.ModuliTowerWitness.tower_laws_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitness.tower_laws_of_two_mul_dvd)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_isLevelIsogeny_of_isLevelIsogeny.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld QuaternionAlgebra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_isLevelIsogeny_of_isLevelIsogeny
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (r : ℕ) (hr : r = q ∨ r = q')
    (u u' : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ))
    (d d' : QM.FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (hud : QM.FakeEllipticCurve.IsLevelIsogeny ℓ u d)
    (huu' : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u u')
    (hu'd' : QM.FakeEllipticCurve.IsLevelIsogeny ℓ u' d') :
    QM.FakeEllipticCurve.IsAtkinLehnerQuotient r d d' := by sorry
