-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isSquare_or_sq_lt_four_mul_of_forall_act_comp_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isSquare_or_sq_lt_four_mul_of_forall_act_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/064aca5f-c567-5d26-9fbe-1f1d38d667ec
-- title:
--   Discriminant of a Λ-equivariant endomorphism is square or negative
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, let $a,b\in\mathbb{Q}$, and assume $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite and ramified exactly at $q,q'$, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible precisely when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order (containing $1$, closed under multiplication, $\mathbb{Q}$-spanning, finitely generated) and maximal among orders, let $N\in\mathbb{N}$, let $k$ be an algebraically closed field, and let $E$ be a fake elliptic curve over $k$ with $\Lambda$-action and level-$N$ data: a scheme $E.A$ with structure morphism $E.f$ to $\operatorname{Spec} k$, a commutative relative group law $E.L$ on its functor of points, the abelian-scheme property bundle (smooth, proper, connected fibres, group law present), fibres of dimension $2$, and an action $E.\mathrm{act}$ of $\Lambda$ by endomorphisms over $\operatorname{Spec} k$. Let $\varphi:E.A\to E.A$ satisfy $\varphi$ followed by $E.f$ equals $E.f$, let $\varphi$ be a homomorphism for $E.L$ on $T$-valued points for every $k$-scheme $T$, and let $E.\mathrm{act}(x)$ followed by $\varphi$ equal $\varphi$ followed by $E.\mathrm{act}(x)$ for all $x\in\Lambda$. Let $t,n\in\mathbb{Z}$ and suppose that in every point group one has $\varphi(\varphi(P))\cdot P^{n}=\varphi(P)^{t}$. Then $t^{2}-4n$ is a square or $t^{2}<4n$.
--
--   This is the statement that an endomorphism of a fake elliptic curve commuting with the quaternionic multiplication cannot generate a real quadratic field: the discriminant of its integral quadratic relation is either a square (so $\varphi$ lies in a split quadratic situation) or negative. It is the input to [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_mapPt_eq_zpow_of_forall_act_comp_eq_of_four_mul_le_sq`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_mapPt_eq_zpow_of_forall_act_comp_eq_of_four_mul_le_sq), which in the non-negative non-square case forces such a $\varphi$ to be an integral power on points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isSquare_or_sq_lt_four_mul_of_forall_act_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isSquare_or_sq_lt_four_mul_of_forall_act_comp_eq
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x)
    (t n : ℤ)
    (hquad : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ (mapPt φ hφ P) * P ^ n = mapPt φ hφ P ^ t) :
    IsSquare (t ^ 2 - 4 * n) ∨ t ^ 2 < 4 * n := by sorry
