-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/b49b9d03-b182-5ef1-a5a2-5e1ddf0d1d77
-- title:
--   Atkin–Lehner quotients are isomorphism-invariant in the source
-- statement:
--   Let $q \neq q'$ be primes and $a,b \in \mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $0 < a$ or $0 < b$, and for a finite place $v$ of $\mathbb{Q}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ lies above $q$ or above $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. an order containing every order that contains it, let $N \neq 0$ be a natural number divisible by neither $q$ nor $q'$, let $r$ be $q$ or $q'$, let $\ell$ be a prime different from $q$ and $q'$, and let $S$ be a commutative ring. Let $u, u_1, u', u_1'$ be objects of `WithExtraLevel Λ N ℓ S`, i.e. pairs consisting of a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ structure `lev` together with an extra level-$\ell$ structure `levK`. Assume $u$ and $u_1$ are isomorphic, in the sense that there is an isomorphism of the underlying schemes over $\operatorname{Spec} S$ compatible with the relative group laws on points, commuting with the $\Lambda$-actions, and matching both the `lev` and the `levK` factorisation conditions in both directions. Assume moreover that $u'$ is an Atkin–Lehner quotient of $u$ at $r$ and $u_1'$ one of $u_1$ at $r$: in each case there are morphisms $\varphi$ and $\psi$ over $S$ between the two underlying schemes, both additive for the relative group laws and $\Lambda$-equivariant, whose two composites are the action of the scalar $r$ whenever $r \in \Lambda$, such that a point is killed by $\varphi$ precisely when it is killed by every $m \in \Lambda$ with $m \, \overline{m} = rn$ for some integer $n$, and such that $\varphi$ carries points factoring through `lev`, respectively `levK`, to points factoring through the corresponding structure of the target. The conclusion is that $u'$ and $u_1'$ are isomorphic in the same sense.
--
--   This is the uniqueness-up-to-isomorphism statement for the Atkin–Lehner quotient at a ramified prime of a fake elliptic curve with extra level structure, in the two-sided form: isomorphic sources have isomorphic quotients, over an arbitrary commutative base ring. It is used in the construction of the Čerednik–Drinfeld comparison, where it feeds the pullback description of the Atkin–Lehner correspondence and the existence of quotient data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (r : ℕ) (hr : r = q ∨ r = q') (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (S : Type) [CommRing S] (u u₁ u' u₁' : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
    (hu : QM.FakeEllipticCurve.WithExtraLevel.Iso u u₁) (h : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u u')
    (h₁ : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u₁ u₁') :
    QM.FakeEllipticCurve.WithExtraLevel.Iso u' u₁' := by sorry
