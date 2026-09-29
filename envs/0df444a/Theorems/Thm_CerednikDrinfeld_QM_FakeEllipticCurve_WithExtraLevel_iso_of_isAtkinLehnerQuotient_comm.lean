-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comm
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isAtkinLehnerQuotient_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/eaef4c74-172f-5dda-b53f-f46ec4b104b3
-- title:
--   Atkin–Lehner quotients at q and q' commute with extra level
-- statement:
--   Fix natural numbers $N \ne 0$ and primes $q, q'$ with $q' \neq q$, neither dividing $N$, and rationals $a, b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order and is maximal among orders under inclusion, and let $\ell$ be a prime distinct from $q$ and $q'$. Let $u, u_1, u_{12}, u_2, u_{21}$ be objects of `WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)`, that is, pairs consisting of a fake elliptic curve over $\overline{\mathbb{Q}}$ (an abelian scheme of relative dimension $2$ with commutative relative group law, an action of $\Lambda$ compatible with the group law and with the prescribed reduced-trace condition, and a level-$N$ structure $\mathrm{lev}$) together with an extra level structure $\mathrm{levK}$ at $\ell$. Assume `IsAtkinLehnerQuotient` holds for $q$ from $u$ to $u_1$, for $q'$ from $u_1$ to $u_{12}$, for $q'$ from $u$ to $u_2$, and for $q$ from $u_2$ to $u_{21}$; for $r$ and $u \to u'$ this asserts the existence of morphisms $\varphi$, $\psi$ over the base in both directions, each a homomorphism for the relative group laws and commuting with the $\Lambda$-actions, with $\varphi$ followed by $\psi$ and $\psi$ followed by $\varphi$ equal to the action of the scalar $r$ whenever $r \in \Lambda$, with the kernel of $\varphi$ on points characterised by annihilation under all $m \in \Lambda$ whose norm $m \, \overline{m}$ is an integral multiple of $r$, and with $\varphi$ carrying points factoring through $\mathrm{lev}$, respectively $\mathrm{levK}$, to points factoring through the corresponding structures on $u'$. The conclusion is `WithExtraLevel.Iso u₁₂ u₂₁`: there is an isomorphism of the underlying schemes over $\mathrm{Spec}\,\overline{\mathbb{Q}}$ compatible with the group laws and the $\Lambda$-actions, under which a point factors through $\mathrm{lev}$ (respectively $\mathrm{levK}$) on $u_{12}$ if and only if its image does on $u_{21}$.
--
--   This is the commutativity of the two Atkin–Lehner (Cherednik–Drinfeld) quotient operations at the two ramified primes $q$, $q'$ of the quaternion algebra, carried out at the upper level of the tower where an additional level structure at $\ell$ is present. It feeds the tower laws for the moduli of fake elliptic curves with extra level, used via [`CerednikDrinfeld.QM.ModuliTowerWitness.tower_laws_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitness.tower_laws_of_two_mul_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isAtkinLehnerQuotient_comm.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld QuaternionAlgebra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isAtkinLehnerQuotient_comm
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (u u₁ u₁₂ u₂ u₂₁ : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ))
    (h₁ : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient q u u₁)
    (h₁₂ : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient q' u₁ u₁₂)
    (h₂ : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient q' u u₂)
    (h₂₁ : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient q u₂ u₂₁) :
    QM.FakeEllipticCurve.WithExtraLevel.Iso u₁₂ u₂₁ := by sorry
