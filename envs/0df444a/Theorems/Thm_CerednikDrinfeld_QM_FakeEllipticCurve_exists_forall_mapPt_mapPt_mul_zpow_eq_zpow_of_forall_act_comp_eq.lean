-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/a4a6179d-157c-59d8-b649-fea45bcdce15
-- title:
--   Endomorphisms commuting with Λ satisfy a quadratic integer relation
-- statement:
--   Let $q$ and $q'$ be primes with $q' \neq q$, and let $a, b \in \mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $a > 0$ or $b > 0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order, that is, $\Lambda$ contains $1$, is closed under multiplication, spans $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$ and is finitely generated, and every order containing $\Lambda$ equals $\Lambda$. Let $N$ be a natural number, $k$ an algebraically closed field, and $E$ a `FakeEllipticCurve Λ N k`, so in particular a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec} k$, a commutative relative group law $E.L$ on the functor of points of $E.f$, the abelian-scheme property bundle (smooth, proper, connected fibres), fibres of topological Krull dimension $2$, and an action $E.\mathrm{act}$ of $\Lambda$ satisfying the trace condition. Let $\varphi : E.A \to E.A$ satisfy $\varphi$ followed by $E.f$ equals $E.f$, assume that for every scheme $T$, every $t : T \to \operatorname{Spec} k$ and all $T$-points $P, Q$ of $E.f$ the map $P \mapsto \varphi \circ P$ carries $E.L.\mathrm{mul}\,t\,P\,Q$ to the product of the images, and assume $E.\mathrm{act}\,x$ followed by $\varphi$ equals $\varphi$ followed by $E.\mathrm{act}\,x$ for every $x \in \Lambda$. Then there exist integers $t$ and $n$ such that for every scheme $T$, every $s : T \to \operatorname{Spec} k$ and every $T$-point $P$ of $E.f$, in the commutative group of such points supplied by $E.L$ one has $\varphi \circ (\varphi \circ P) \cdot P^{n} = (\varphi \circ P)^{t}$.
--
--   This is the integrality half of the classical structure theorem for the commutant of a quaternionic multiplication: every endomorphism of a fake elliptic curve commuting with the action of the maximal order $\Lambda$ satisfies a monic quadratic equation $\varphi^2 - t\varphi + n = 0$ over $\mathbb{Z}$ in the endomorphism ring. It is used to show that such endomorphisms which are automorphisms have finite order, and in the finiteness statement enumerating fake elliptic curves up to isomorphism in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_mapPt_mapPt_mul_zpow_eq_zpow_of_forall_act_comp_eq
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x) :
    ∃ t n : ℤ, ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ (mapPt φ hφ P) * P ^ n = mapPt φ hφ P ^ t := by sorry
