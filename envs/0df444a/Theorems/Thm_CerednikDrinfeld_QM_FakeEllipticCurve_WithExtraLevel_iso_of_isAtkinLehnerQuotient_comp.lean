-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isAtkinLehnerQuotient_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/58fc1c01-60ec-54e2-bf5d-0e60972fd4e1
-- title:
--   Twice-iterated Atkin–Lehner quotient with extra level is trivial
-- statement:
--   Fix a natural number $N \neq 0$ and primes $q, q'$ with $q' \neq q$, neither dividing $N$, and rationals $a, b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order maximal among orders, let $\ell$ be a prime distinct from $q$ and $q'$, and let $r$ be $q$ or $q'$. Let $u, u', u''$ be triples consisting of a fake elliptic curve over $\overline{\mathbb{Q}}$ with $\Lambda$-action and level-$N$ structure in the sense of `FakeEllipticCurve Λ N`, each equipped with an extra level structure at $\ell$. Assume `WithExtraLevel.IsAtkinLehnerQuotient r u u'` and `WithExtraLevel.IsAtkinLehnerQuotient r u' u''`: in each case there are morphisms $\varphi$ and $\psi$ between the underlying schemes, over $\operatorname{Spec} \overline{\mathbb{Q}}$ in both directions, each additive for the relative group laws and commuting with the $\Lambda$-actions, with $\varphi$ followed by $\psi$ and $\psi$ followed by $\varphi$ equal to the action of $r$ whenever $r \in \Lambda$, such that on $T$-points the image of $P$ under $\varphi$ is the identity section precisely when $P$ is killed by every $m \in \Lambda$ with $m\,\overline{m}$ an integer multiple of $r$, and such that $\varphi$ carries points factoring through the level-$N$ subscheme, respectively through the extra level-$\ell$ subscheme, to points factoring through the corresponding subscheme of the target. The conclusion is `WithExtraLevel.Iso u u''`: there is an isomorphism $e$ of the underlying schemes over $\operatorname{Spec} \overline{\mathbb{Q}}$ which is additive for the relative group laws, commutes with the $\Lambda$-actions, and for which factoring through the level-$N$ subscheme, and likewise through the extra level-$\ell$ subscheme, is preserved in both directions.
--
--   This is the statement that the Atkin–Lehner involution at a prime $r$ ramified in the quaternion algebra squares to the identity, formulated on the moduli of fake elliptic curves with level-$N$ structure and extra level at $\ell$, i.e. on the Shimura curve of level $\Gamma_0(N) \cap \Gamma^0(\ell)$; the underlying arithmetic input is that the two-sided ideal of elements of $\Lambda$ of reduced norm divisible by $r$ has square $r\Lambda$. It supplies the involution law used by [`CerednikDrinfeld.QM.ModuliTowerWitness.tower_laws_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitness.tower_laws_of_two_mul_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comp.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld QuaternionAlgebra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isAtkinLehnerQuotient_comp
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (r : ℕ) (hr : r = q ∨ r = q')
    (u u' u'' : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ))
    (h : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u u')
    (h' : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u' u'') :
    QM.FakeEllipticCurve.WithExtraLevel.Iso u u'' := by sorry
