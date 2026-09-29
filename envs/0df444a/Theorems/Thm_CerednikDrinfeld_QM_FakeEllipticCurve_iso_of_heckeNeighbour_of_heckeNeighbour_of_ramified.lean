-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_heckeNeighbour_of_heckeNeighbour_of_ramified
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_heckeNeighbour_of_heckeNeighbour_of_ramified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/3bdf943e-7bdf-5958-933c-a3280ecd54da
-- title:
--   Uniqueness of r-Hecke neighbours at a ramified prime
-- statement:
--   Fix natural numbers $N \ne 0$ and primes $q \neq q'$ with $q \nmid N$ and $q' \nmid N$, and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $a > 0$ or $b > 0$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $q \in v$ or $q' \in v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order (containing $1$, multiplicatively closed, finitely generated, with $\mathbb{Q}$-span everything) and is maximal among orders for inclusion, and let $r$ be $q$ or $q'$. Let $E,E',E''$ be fake elliptic curves for $\Lambda$ and level $N$ over $\overline{\mathbb{Q}}$: smooth proper schemes with connected fibres of Krull dimension $2$ over the base, equipped with a commutative relative group law, an action of $\Lambda$ by base-preserving endomorphisms compatible with the group law, additive and multiplicative in $\Lambda$ and satisfying the trace condition on tangent spaces, together with a level morphism `lev`. Assume $E'$ and $E''$ are both $r$-Hecke neighbours of $E$, i.e. in each case there are mutually inverse-up-to-$r$ maps over the base, compatible with the group laws, commuting with the $\Lambda$-actions, preserving factorisation of points through `lev` in both directions, with the two composites equal to the action of $r \in \Lambda$ when $r$ lies in $\Lambda$, and with neither map an isomorphism. Then $E'$ and $E''$ are isomorphic: there is an isomorphism of their underlying schemes over the base which is compatible with the group laws, commutes with the $\Lambda$-actions, and matches factorisation through the respective level morphisms in both directions.
--
--   This is the uniqueness of the Hecke neighbour at a prime $r$ at which the indefinite quaternion algebra ramifies, reflecting the fact that the maximal order of a ramified local quaternion division algebra has a unique two-sided ideal above $r$, so that the $r$-torsion of a fake elliptic curve has a unique proper nonzero $\Lambda$-stable subgroup. It feeds the moduli-tower comparison used on the Čerednik–Drinfel'd side, being cited by [`CerednikDrinfeld.QM.ModuliTowerWitness.eq_smul_iff_heckeNeighbour_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitness.eq_smul_iff_heckeNeighbour_of_two_mul_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_heckeNeighbour_of_heckeNeighbour_of_ramified.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_heckeNeighbour_of_heckeNeighbour_of_ramified
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q')
    (E E' E'' : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (h' : FakeEllipticCurve.HeckeNeighbour r E E') (h'' : FakeEllipticCurve.HeckeNeighbour r E E'') :
    FakeEllipticCurve.Iso E' E'' := by sorry
