-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_setOf_forall_pushPt_act_eq_one_of_eq_or_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.natCard_setOf_forall_pushPt_act_eq_one_of_eq_or_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/aee4ca57-c05e-5755-836a-9a054d623ce6
-- title:
--   Order r² for mathfrak Pᵣ-torsion of fake elliptic curves
-- statement:
--   Fix rationals $a,b$ and primes $q,q'$ with $q'\neq q$, and suppose `IsIndefiniteRamifiedExactlyAt a b q q'` holds for the quaternion algebra $B=\mathbb H[\mathbb Q,a,b]$: that is, $0<a$ or $0<b$, and for each height-one prime $v$ of the ring of integers of $\mathbb Q$ the completion $B\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq B$ be a $\mathbb Z$-submodule that is a maximal order, i.e. it contains $1$, is closed under multiplication, spans $B$ over $\mathbb Q$, is finitely generated, and is maximal among submodules with these properties. Let $N$ be a natural number, $k$ an algebraically closed field, and $E$ a `FakeEllipticCurve Λ N k`: a scheme $A$ with structure morphism `E.f` to $\operatorname{Spec} k$, a commutative relative group law `E.L`, the abelian-scheme property bundle (smooth, proper, connected fibres, a group law), fibres of topological Krull dimension $2$, an action `E.act` of $\Lambda$ by endomorphisms of $A$ over the base that is additive and multiplicative and satisfies the prescribed trace condition on tangent vectors, together with the further level-$N$ data of the structure. Let $r$ be a natural number with $r=q$ or $r=q'$, and assume $r\neq 0$ in $k$. Then the set of sections $P$ of `E.f` over the identity of $\operatorname{Spec} k$ (morphisms $\operatorname{Spec} k\to A$ composing with `E.f` to the identity, i.e. $k$-points of $A$) such that for every $m\in\Lambda$ and every integer $n$ with $m\,\overline m=rn$ in $B$ the point $P$ followed by `E.act m` is the identity section `E.L.one`, is finite of cardinality exactly $r^2$.
--
--   This is the statement that on a fake elliptic curve with $\Lambda$-action in residue characteristic different from $r$, the subgroup of $k$-points annihilated by the two-sided prime $\mathfrak P_r=\{m\in\Lambda: m\overline m\in r\mathbb Z\}$ of the maximal order above a ramified prime $r\in\{q,q'\}$ has order $r^2$, reflecting that $\Lambda/\mathfrak P_r$ is a field with $r^2$ elements and that the $r$-torsion is free of rank one over $\Lambda/r\Lambda$. It is used in the identification of the quotient of the relevant moduli by the Atkin–Lehner involution, in [`CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_quotients_of_card_eq_mul_sq`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_quotients_of_card_eq_mul_sq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_natCard_setOf_forall_pushPt_act_eq_one_of_eq_or_eq.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.natCard_setOf_forall_pushPt_act_eq_one_of_eq_or_eq
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q) (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (r : ℕ) (hr : r = q ∨ r = q') (hrk : (r : k) ≠ 0) :
    Nat.card {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f //
      ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
        pushPt (E.act m) (E.act_over m) P = E.L.one (𝟙 (Spec (CommRingCat.of k)))} = r ^ 2 := by sorry
