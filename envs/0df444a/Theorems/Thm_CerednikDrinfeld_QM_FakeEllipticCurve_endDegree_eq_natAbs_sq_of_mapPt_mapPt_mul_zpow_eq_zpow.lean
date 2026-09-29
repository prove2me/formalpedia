-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_endDegree_eq_natAbs_sq_of_mapPt_mapPt_mul_zpow_eq_zpow
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.endDegree_eq_natAbs_sq_of_mapPt_mapPt_mul_zpow_eq_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/629752de-d942-512b-8694-78f198aa41eb
-- title:
--   Degree n² for quaternionic endomorphisms with t²<4n
-- statement:
--   Fix distinct primes $q'\neq q$ and rationals $a,b$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, i.e. $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ that is an order maximal among orders under inclusion, let $N$ be a natural number, let $k$ be an algebraically closed field of characteristic zero, and let $E$ be a `FakeEllipticCurve Λ N k`: a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec} k$, a commutative relative group law $E.L$ on its functor of points $\mathrm{SchemeHomOver}$, an abelian-scheme property bundle, two-dimensional fibres, and an action `E.act` of $\Lambda$ by endomorphisms over $k$ with the stated additivity and multiplicativity properties. Let $t,n$ be integers with $t^2<4n$, and let $\varphi : E.A \to E.A$ satisfy $\varphi$ followed by $E.f$ equals $E.f$, together with: composition with $\varphi$ is additive on $T$-points for every $T \to \operatorname{Spec} k$; $\varphi$ commutes with `E.act x` for every $x\in\Lambda$; and, in the commutative group of $T$-points, $\varphi_*(\varphi_* P)\cdot P^{\,n} = (\varphi_* P)^{\,t}$ for all $P$. Then `E.L.endDegree ⟨φ, hφ⟩`, the degree of $\varphi$ as an endomorphism — the rank at the closed point of $\operatorname{Spec} k$ of the kernel scheme of $\varphi$ when that kernel is finite, and $0$ otherwise — equals $|n|^2$.
--
--   This is the classical computation that an endomorphism of an abelian surface with quaternionic multiplication whose characteristic relation $\varphi^2-t\varphi+n=0$ has irreducible characteristic polynomial ($t^2<4n$) has degree $n^2$, obtained from the polynomial behaviour and multiplicativity of the degree on an abelian variety. It is used in the construction of the Čerednik–Drinfeld theory of fake elliptic curves, in particular by [`CerednikDrinfeld.QM.FakeEllipticCurve.finite_and_natCard_mapPt_eq_one_of_mapPt_mapPt_mul_zpow_eq_zpow`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.finite_and_natCard_mapPt_eq_one_of_mapPt_mapPt_mul_zpow_eq_zpow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_endDegree_eq_natAbs_sq_of_mapPt_mapPt_mul_zpow_eq_zpow.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.endDegree_eq_natAbs_sq_of_mapPt_mapPt_mul_zpow_eq_zpow
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
    E.L.endDegree ⟨φ, hφ⟩ = n.natAbs ^ 2 := by sorry
