-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isAtkinLehnerQuotient_comp
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isAtkinLehnerQuotient_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/85f56007-fc94-55cd-983a-461798e6d530
-- title:
--   Composing two Atkin–Lehner quotients recovers the curve
-- statement:
--   Let $q \neq q'$ be primes, let $a,b \in \mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, that is, $0 < a$ or $0 < b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among orders for inclusion, let $N \neq 0$ be a natural number divisible by neither $q$ nor $q'$, and let $r$ be $q$ or $q'$. Let $S$ be a commutative ring and let $E, E', E''$ be fake elliptic curves over $S$ of level $(\Lambda, N)$: relative group schemes $A \to \operatorname{Spec} S$ carrying a commutative relative group law, the abelian-scheme property bundle, fibres of dimension $2$, an action of $\Lambda$ by group-law endomorphisms over $S$ satisfying the additivity, multiplicativity and trace conditions, together with the level datum `lev`. Assume $E'$ is an Atkin–Lehner quotient of $E$ at $r$ and $E''$ one of $E'$ at $r$, in the sense that there are mutually "dual" morphisms $\varphi : E.A \to E'.A$, $\psi : E'.A \to E.A$ over $S$, additive on $T$-points for all $S$-schemes $T$, commuting with the $\Lambda$-actions, whose composites (in either order) are the action of the integer $r$ whenever $r \in \Lambda$, whose kernel on $T$-points is cut out by the condition that all $m \in \Lambda$ with $m \bar m \in r\mathbb{Z}$ annihilate the point, and which preserve the property of factoring through `lev`; and similarly for $E' \to E''$. Then $E$ and $E''$ are isomorphic as fake elliptic curves: there is an isomorphism $e : E.A \cong E''.A$ over $S$, additive on $T$-points, commuting with the $\Lambda$-actions, and such that a $T$-point of $E$ factors through $E.\mathrm{lev}$ if and only if its image under $e$ factors through $E''.\mathrm{lev}$.
--
--   This is the involutivity of the Atkin–Lehner operator $w_r$ at a prime $r$ ramified in the quaternion algebra, in the moduli-theoretic form: dividing twice by the kernel of the two-sided ideal above $r$ amounts to dividing by $[r]$, hence returns an isomorphic object. It is stated over an arbitrary commutative base ring, and is used in the construction of the Atkin–Lehner involution on the coarse moduli space of fake elliptic curves, where the uniqueness property of the coarse moduli space quantifies over all base rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isAtkinLehnerQuotient_comp.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isAtkinLehnerQuotient_comp
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (r : ℕ) (hr : r = q ∨ r = q')
    (S : Type) [CommRing S] (E E' E'' : QM.FakeEllipticCurve Λ N S)
    (h : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E E') (h' : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E' E'') :
    QM.FakeEllipticCurve.Iso E E'' := by sorry
