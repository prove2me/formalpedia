-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isAtkinLehnerQuotient
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isAtkinLehnerQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/ef258b52-d2be-5fd3-97b8-11b992d8767c
-- title:
--   Atkin–Lehner quotients exist for fake elliptic curves with extra level
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. an order containing every order that contains it, let $N$ be a nonzero natural number prime to $q$ and to $q'$, let $r$ be $q$ or $q'$, and let $\ell$ be a prime distinct from $q$ and $q'$. Then for every commutative ring $S$ and every pair $u = (E,K)$ consisting of a fake elliptic curve $E$ over $S$ of level $N$ for $\Lambda$ and an extra level structure $K$ of level $\ell$ on $E$, there is a further such pair $u'$ with `WithExtraLevel.IsAtkinLehnerQuotient r u u'`: there are $S$-morphisms $\varphi : E.A \to E'.A$ and $\psi : E'.A \to E.A$, additive on $T$-valued points for the two relative group laws, commuting with the $\Lambda$-actions, such that if the scalar $r$ lies in $\Lambda$ then the composite of $\varphi$ followed by $\psi$ is the action of $r$ on $E$ and the composite of $\psi$ followed by $\varphi$ is the action of $r$ on $E'$; moreover a point $P$ of $E$ is killed by $\varphi$ precisely when it is killed by the action of every $m \in \Lambda$ with $m \, \bar m = rn$ for some integer $n$, and $\varphi$ carries points factoring through the level structure $E.\mathrm{lev}$, respectively through $K$, to points factoring through $E'.\mathrm{lev}$, respectively through the extra level structure of $u'$.
--
--   This is the moduli-theoretic construction of the Atkin–Lehner operator at a prime $r$ where the indefinite quaternion algebra ramifies: the quotient of a fake elliptic curve with $\Gamma$-structure by the kernel of the two-sided prime $\mathfrak{P}_r$ of the maximal order, together with the image of the auxiliary $\ell$-level structure. It serves the Čerednik–Drinfeld analysis of Shimura curves and is used in [`CerednikDrinfeld.QM.exists_WT_of_coarse_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.exists_WT_of_coarse_of_two_mul_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isAtkinLehnerQuotient.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isAtkinLehnerQuotient
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (r : ℕ) (hr : r = q ∨ r = q') (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (S : Type) [CommRing S] (u : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S) :
    ∃ u' : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S, QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u u' := by sorry
