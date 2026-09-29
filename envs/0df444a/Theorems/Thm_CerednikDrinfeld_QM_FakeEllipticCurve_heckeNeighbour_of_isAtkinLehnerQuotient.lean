-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_heckeNeighbour_of_isAtkinLehnerQuotient
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.heckeNeighbour_of_isAtkinLehnerQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/1a64a50a-64f8-5b52-be84-1acb48f9f8b3
-- title:
--   Atkin–Lehner quotients at a ramified prime are Hecke neighbours
-- statement:
--   Let $q,q'$ be primes, let $a,b\in\mathbb Q$, and suppose $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, that is, $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra (every nonzero element a unit) exactly when $q$ or $q'$ lies in $v$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is an order maximal among orders under inclusion, let $N,r$ be naturals with $r=q$ or $r=q'$ and $r\nmid N$, and let $E,E'$ be fake elliptic curves of level $N$ over $\overline{\mathbb Q}$ for $(\Lambda,N)$: abelian schemes with commutative relative group law, two-dimensional fibres, a $\Lambda$-action by base-preserving endomorphisms that is additive and multiplicative and respects the group law and the reduced-trace normalisation, together with a level subscheme $\mathrm{lev}$. Assume `IsAtkinLehnerQuotient r E E'`: there are base-preserving $\varphi:E\to E'$ and $\psi:E'\to E$, homomorphisms for the group laws on $T$-points and commuting with the $\Lambda$-actions, with $\varphi\psi=[r]$ and $\psi\varphi=[r]$ whenever $r\in\Lambda$, such that $\varphi$ kills exactly those points annihilated by all $m\in\Lambda$ of reduced norm divisible by $r$, and $\varphi$ carries points factoring through $E.\mathrm{lev}$ into $E'.\mathrm{lev}$. Then `HeckeNeighbour r E E'` holds: such a pair $\varphi,\psi$ exists with levels carried in both directions and with neither $\varphi$ nor $\psi$ an isomorphism.
--
--   This is the statement that, at a prime $r$ at which the indefinite quaternion algebra ramifies, the Atkin–Lehner quotient of a fake elliptic curve is an $r$-Hecke neighbour of it: beyond the quotient data one must produce the level-structure compatibility for the dual isogeny and rule out invertibility, the latter resting on the fact that the two-sided maximal ideal at $r$ has square $r\Lambda_r$. It feeds the moduli-tower comparison [`CerednikDrinfeld.QM.ModuliTowerWitness.eq_smul_iff_heckeNeighbour_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitness.eq_smul_iff_heckeNeighbour_of_two_mul_dvd) and the construction of descent intertwining data in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_heckeNeighbour_of_isAtkinLehnerQuotient.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.heckeNeighbour_of_isAtkinLehnerQuotient
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N r : ℕ) (hr : r = q ∨ r = q') (hrN : ¬ r ∣ N)
    (E E' : QM.FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (h : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E E') :
    QM.FakeEllipticCurve.HeckeNeighbour r E E' := by sorry
