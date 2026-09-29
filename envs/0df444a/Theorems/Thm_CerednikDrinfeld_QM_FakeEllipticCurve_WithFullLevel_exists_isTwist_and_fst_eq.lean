-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isTwist_and_fst_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isTwist_and_fst_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/9ddbe544-d3c0-58d7-83a2-c0f2a94d21c8
-- title:
--   Twisting a full level-m structure by a unit mod mΛ
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order in the sense of `IsOrder`: it contains $1$, is closed under multiplication, spans the quaternion algebra over $\mathbb{Q}$, and is finitely generated. Fix natural numbers $N,m$ and a commutative ring $S$, and let $u$ be an element of `FakeEllipticCurve.WithFullLevel Λ N m S`, that is, a pair consisting of a fake elliptic curve $E$ over $S$ with $\Lambda$-action in the sense of `FakeEllipticCurve` together with a full level-$m$ structure on it, i.e. an $S$-point $P$ of $E$ killed by $m$ for the relative group law, whose $\Lambda$-orbit at every geometric point of $S$ exhausts the $m$-torsion, and whose annihilator in $\Lambda$ is exactly $m\Lambda$. Let $c,d\in\Lambda$ satisfy $cd-1\in m\Lambda$ and $dc-1\in m\Lambda$, each expressed as $m$ times an element of $\Lambda$. Then there exists $u'$ in `FakeEllipticCurve.WithFullLevel Λ N m S` whose underlying fake elliptic curve is literally that of $u$, and such that `WithFullLevel.IsTwist c u u'` holds: there is an isomorphism of the underlying schemes over $\operatorname{Spec} S$ that respects the relative group laws, commutes with the action of every $x\in\Lambda$, matches the factorisation through the level structure morphism `lev` on points, and carries $c\cdot P$ to the level structure point of $u'$.
--
--   This is the statement that a unit of $\Lambda/m\Lambda$ acts on full level-$m$ structures of a fixed fake elliptic curve, the twisted structure living on the same curve; it underlies the definition of the level-twisting action on the fine moduli problem for quaternionic (fake elliptic) curves. It is used in the construction of coarse moduli as a quotient by this action and in the equivariance statements for pullbacks of the fine moduli scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isTwist_and_fst_eq.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isTwist_and_fst_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N m : ℕ} {S : Type} [CommRing S]
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (c d : ↥Λ)
    (hcd : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b]))
    (hdc : ∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    ∃ u' : FakeEllipticCurve.WithFullLevel Λ N m S, FakeEllipticCurve.WithFullLevel.IsTwist c u u' ∧ u'.1 = u.1 := by sorry
