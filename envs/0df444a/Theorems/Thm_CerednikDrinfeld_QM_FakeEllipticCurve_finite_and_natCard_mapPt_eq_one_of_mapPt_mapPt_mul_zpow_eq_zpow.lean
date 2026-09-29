-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finite_and_natCard_mapPt_eq_one_of_mapPt_mapPt_mul_zpow_eq_zpow
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.finite_and_natCard_mapPt_eq_one_of_mapPt_mapPt_mul_zpow_eq_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/718ce002-a4c7-5dac-8f05-c4c6b693116a
-- title:
--   Kernel of a quadratic endomorphism has n² points
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, and let $a,b$ be rationals such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order (containing $1$, closed under multiplication, $\mathbb{Q}$-spanning, finitely generated) and maximal among orders containing it, let $N$ be a natural number, let $k$ be an algebraically closed field of characteristic zero, and let $E$ be a `FakeEllipticCurve Λ N k`: a scheme $E.A$ with structure morphism $E.f$ to $\operatorname{Spec} k$, a commutative relative group law $E.L$ on its $T$-points, the properties smooth, proper, connected fibres and existence of a group law, all fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over $k$ compatible with the group law, additivity and the trace condition, together with the further data of the structure. Let $t,n$ be integers with $t^2<4n$, and let $\varphi: E.A\to E.A$ be a morphism over $\operatorname{Spec} k$ ($\varphi$ followed by $E.f$ equals $E.f$) such that composition with $\varphi$ is additive on $T$-points for every $k$-scheme $T$, such that $\varphi$ commutes with the action of every element of $\Lambda$, and such that for every $s:T\to\operatorname{Spec} k$ and every $T$-point $P$ of $E.f$ one has $\varphi(\varphi(P))\cdot P^{n}=\varphi(P)^{t}$ in the commutative group of $T$-points. Then the set of $k$-points of $E.f$ (sections over the identity of $\operatorname{Spec} k$) killed by $\varphi$, i.e. sent to the identity section, is finite, and its cardinality is $|n|^2$.
--
--   This is the point count of the kernel of an endomorphism $\varphi$ of a fake elliptic curve satisfying the quadratic relation $\varphi^2-[t]\varphi+[n]=0$ with $t^2<4n$: over an algebraically closed field of characteristic zero the kernel is étale, so the number of its $k$-points equals the degree $n^2$. It feeds the construction of chains of level isogenies and Atkin–Lehner quotients for fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finite_and_natCard_mapPt_eq_one_of_mapPt_mapPt_mul_zpow_eq_zpow.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.finite_and_natCard_mapPt_eq_one_of_mapPt_mapPt_mul_zpow_eq_zpow
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (E : FakeEllipticCurve Λ N k)
    (t n : ℤ) (htn : t ^ 2 < 4 * n)
    (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hadd : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver s E.f),
      mapPt φ hφ (E.L.mul s P Q) = E.L.mul s (mapPt φ hφ P) (mapPt φ hφ Q))
    (hlin : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x)
    (hrel : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ (mapPt φ hφ P) * P ^ n = mapPt φ hφ P ^ t) :
    Finite {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f //
        mapPt φ hφ P = E.L.one (𝟙 (Spec (CommRingCat.of k)))} ∧
    Nat.card {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f //
        mapPt φ hφ P = E.L.one (𝟙 (Spec (CommRingCat.of k)))} = n.natAbs ^ 2 := by sorry
