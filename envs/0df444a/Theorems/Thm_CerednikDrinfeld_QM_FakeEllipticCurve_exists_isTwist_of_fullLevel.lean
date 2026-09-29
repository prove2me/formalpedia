-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isTwist_of_fullLevel
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isTwist_of_fullLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/9d7796fa-103f-52fe-9375-f759c5e9f6a9
-- title:
--   Two full level-m structures differ by a twist
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of `IsOrder`: $1\in\Lambda$, $\Lambda$ is closed under multiplication, its $\mathbb{Q}$-span is everything, and it is finitely generated. Fix natural numbers $N$ and $m$, an algebraically closed field $k$, a fake elliptic curve $E$ of level $N$ with $\Lambda$-action over $k$ (a scheme $A$ with structure morphism $f$ to $\operatorname{Spec} k$, a commutative relative group law, the abelian-scheme property bundle, two-dimensional fibres, an action of $\Lambda$ by endomorphisms over $\operatorname{Spec} k$, and the level datum $C\to A$), and two full level-$m$ structures $P,P'$ on $E$, i.e. sections over $\operatorname{Spec} k$ killed by $m$ whose $\Lambda$-orbit exhausts the $m$-torsion at every geometric point and whose annihilator in $\Lambda$ is exactly $m\Lambda$. The conclusion asserts the existence of $c,d\in\Lambda$ with $cd-1\in m\Lambda$ and $dc-1\in m\Lambda$ (each witnessed by some $y\in\Lambda$ with the stated equality in $\mathbb{H}[\mathbb{Q},a,b]$) such that $\langle E,P\rangle$ and $\langle E,P'\rangle$ are related by `WithFullLevel.IsTwist c`: there is an isomorphism $e$ of $A$ over $\operatorname{Spec} k$ which is additive for the relative group law on points, commutes with the action of every $x\in\Lambda$, preserves the property of a point factoring through the level morphism, and carries the translate of $P$ by the action of $c$ to $P'$.
--
--   This is the statement that, over an algebraically closed field, the group of units of $\Lambda/m\Lambda$ acts transitively on the full level-$m$ structures of a fixed fake elliptic curve, the twisting element $c$ being determined modulo $m\Lambda$ up to the stated two-sided congruence. It is used in the fine-moduli analysis of the quaternionic moduli problem, specifically in [`CerednikDrinfeld.QM.IsFineModuli.nilpPoints_quotient_surjective_and_iff_of_isAlgClosed_of_isMaximalOrder`](thm.html#CerednikDrinfeld.QM.IsFineModuli.nilpPoints_quotient_surjective_and_iff_of_isAlgClosed_of_isMaximalOrder).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isTwist_of_fullLevel.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isTwist_of_fullLevel
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N : ℕ} {m : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k]
    (E : FakeEllipticCurve Λ N k) (P P' : E.FullLevel m) :
    ∃ c d : ↥Λ,
      (∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      FakeEllipticCurve.WithFullLevel.IsTwist c (⟨E, P⟩ : FakeEllipticCurve.WithFullLevel Λ N m k) ⟨E, P'⟩ := by sorry
