-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/37b81938-fbe7-59a7-87e5-a1a1c49db06a
-- title:
--   Uniqueness of the Atkin–Lehner quotient with extra level at ℓ
-- statement:
--   Fix natural numbers $N \ge 1$ and primes $q, q'$ with $q \nmid N$, $q' \nmid N$ and $q' \neq q$, and rationals $a, b$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for $\mathbb H[\mathbb Q, a, b]$: $0 < a$ or $0 < b$, and for every height-one prime $v$ of the ring of integers of $\mathbb Q$, every nonzero element of $\mathbb H[\mathbb Q,a,b] \otimes_{\mathbb Q} \mathbb Q_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is an order maximal among the orders containing it, let $\ell$ be a prime with $\ell \neq q$ and $\ell \neq q'$, and let $r = q$ or $r = q'$. Let $u, u', u''$ be objects of `WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)`, i.e. pairs consisting of a fake elliptic curve over $\overline{\mathbb Q}$ (a scheme with structure morphism to the base, a commutative relative group law, the abelian-scheme property bundle, two-dimensional fibres, an action of $\Lambda$ by base-preserving additive endomorphisms satisfying the trace condition, and a level-$N$ structure `lev`) together with an extra level structure `levK` at $\ell$. Assume `WithExtraLevel.IsAtkinLehnerQuotient r u u'` and `WithExtraLevel.IsAtkinLehnerQuotient r u u''`: in each case there are morphisms $\varphi$ from $u$ and $\psi$ back, over the base, both compatible with the group laws and commuting with the $\Lambda$-actions, with $\varphi$ followed by $\psi$ and $\psi$ followed by $\varphi$ equal to the action of $r$ whenever $r \in \Lambda$, such that a point is killed by $\varphi$ precisely when it is killed by every $m \in \Lambda$ with $m \, \overline{m} = rn$ for some integer $n$, and such that $\varphi$ sends points factoring through `lev` and through `levK` to points factoring through the corresponding structures of the target. Then `WithExtraLevel.Iso u' u''` holds: there is an isomorphism of schemes $u'.A \cong u''.A$ over the base which is compatible with the group laws, commutes with the $\Lambda$-actions, and for which a point factors through `lev` (respectively `levK`) of $u'$ if and only if its image factors through `lev` (respectively `levK`) of $u''$.
--
--   This is the uniqueness, up to isomorphism of pairs, of the Atkin–Lehner quotient at a ramified prime $r \in \{q,q'\}$ on the floor of the moduli problem carrying an extra level structure at $\ell$ — the statement that the quotient of a fake elliptic curve by the kernel of the two-sided ideal above $r$ is determined by the data it quotients. It is used in the comparison of two descriptions of a place in the level-$\ell$ tower, in [`CerednikDrinfeld.QM.ModuliTowerWitness.tower_laws_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitness.tower_laws_of_two_mul_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld QuaternionAlgebra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isAtkinLehnerQuotient_of_isAtkinLehnerQuotient
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (r : ℕ) (hr : r = q ∨ r = q')
    (u u' u'' : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ))
    (h' : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u u')
    (h'' : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u u'') :
    QM.FakeEllipticCurve.WithExtraLevel.Iso u' u'' := by sorry
