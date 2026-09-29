-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isOfFinOrder_of_forall_act_comp_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isOfFinOrder_of_forall_act_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/69a3c31e-3685-5fab-8881-c635d4e5313e
-- title:
--   Automorphisms commuting with the quaternionic action have finite order
-- statement:
--   Let $q$ and $q'$ be primes with $q' \neq q$, and let $a,b \in \mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit precisely when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order: it contains $1$, is closed under multiplication, is finitely generated, spans $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$, and every order containing it equals it. Let $N \in \mathbb{N}$, let $k$ be an algebraically closed field, and let $E$ be a fake elliptic curve of level $N$ over $k$ for $\Lambda$: a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec} k$ which is smooth, proper and has connected fibres of dimension $2$, a commutative relative group law $E.L$ on the functor of points over $\operatorname{Spec} k$, an action $E.act$ of $\Lambda$ by endomorphisms over $\operatorname{Spec} k$ which is additive, multiplicative and satisfies the trace condition relating $\Lambda$-reduced traces to traces on the tangent space, together with the further curve and level data carried by the structure. Let $e$ be an automorphism of the scheme $E.A$ such that $e$ followed by $E.f$ is $E.f$, such that for every scheme $T$, every morphism $t : T \to \operatorname{Spec} k$ and all $T$-points $P,Q$ of $E.A$ over $t$, post-composition with $e$ carries $E.L$-products to $E.L$-products, and such that for every $x \in \Lambda$ the morphisms $E.act\,x$ and $e$ commute. Then $e$ is of finite order in the automorphism group of $E.A$, i.e. some positive power of $e$ is the identity.
--
--   This is the finiteness half of the rigidity of fake elliptic curves: the group of automorphisms of the abelian surface commuting with the maximal-order action is a torsion group, reflecting that the $\Lambda$-equivariant endomorphism ring is an order in a division algebra with positive definite norm form. It is used in the rigidity statement [`CerednikDrinfeld.QM.FakeEllipticCurve.eq_one_of_forall_nsmulPt_eq_one_imp_mapPt_eq_of_three_le`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.eq_one_of_forall_nsmulPt_eq_one_imp_mapPt_eq_of_three_le), which shows that an equivariant automorphism fixing enough torsion is the identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isOfFinOrder_of_forall_act_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isOfFinOrder_of_forall_act_comp_eq
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (e : Aut E.A) (he : e.hom ≫ E.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt e.hom he (E.L.mul t P Q) = E.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (hact : ∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E.act x) :
    IsOfFinOrder e := by sorry
