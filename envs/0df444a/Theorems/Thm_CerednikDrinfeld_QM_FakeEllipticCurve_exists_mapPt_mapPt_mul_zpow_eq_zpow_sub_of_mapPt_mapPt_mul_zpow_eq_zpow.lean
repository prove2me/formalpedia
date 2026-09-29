-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mapPt_mapPt_mul_zpow_eq_zpow_sub_of_mapPt_mapPt_mul_zpow_eq_zpow
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_mapPt_mapPt_mul_zpow_eq_zpow_sub_of_mapPt_mapPt_mul_zpow_eq_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/dcd5f8a7-6961-5d66-a746-0e3c0722951a
-- title:
--   Translating an endomorphism: ψ=φ-[k] and its quadratic relation
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order, i.e. contains $1$, is closed under multiplication, spans the quaternion algebra over $\mathbb{Q}$ and is finitely generated. Let $N$ be a natural number, $S$ a commutative ring and $E$ a `FakeEllipticCurve Λ N S`: in particular a scheme $E.A$ with structure morphism $E.f : E.A \to \operatorname{Spec} S$, a relative group law $E.L$ on the functor of points of $E.f$ which is commutative, together with the remaining data of that structure (abelian-scheme properties, fibres of dimension $2$, an action `E.act` of $\Lambda$ by endomorphisms over $S$, and the curve $C$ and further components). Let $t,n,k\in\mathbb{Z}$ and let $\varphi : E.A \to E.A$ satisfy $E.f \circ \varphi = E.f$, so that post-composition $P \mapsto \varphi\circ P$ sends points of $E.f$ over $s : T \to \operatorname{Spec} S$ to points over $s$. Assume: for all such $T$, $s$ and all points $P,Q$, this operation respects the group law $E.L$; for every $x \in \Lambda$, $\varphi$ commutes with `E.act x`; and for all $T$, $s$ and $P$, in the commutative group of points over $s$ furnished by $E.L$ and its commutativity, $\varphi(\varphi(P))\cdot P^{n} = \varphi(P)^{t}$. Then there exists $\psi : E.A \to E.A$ with $E.f \circ \psi = E.f$ which likewise respects the group law on points, commutes with `E.act x` for every $x \in \Lambda$, satisfies $\psi(P) = \varphi(P)\cdot P^{-k}$ for all $T$, $s$ and $P$, and satisfies $\psi(\psi(P))\cdot P^{\,k^{2}-tk+n} = \psi(P)^{\,t-2k}$ for all $T$, $s$ and $P$.
--
--   This is the translation $\psi = \varphi - [k]$ of an endomorphism satisfying the quadratic relation $X^{2}-tX+n$, the resulting relation for $\psi$ being the one with characteristic polynomial $(X+k)^{2}-t(X+k)+n = X^{2}-(t-2k)X+(k^{2}-tk+n)$. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_finset_forall_not_iso_not_exists_mapPt_mapPt_mul_zpow_eq_zpow`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_finset_forall_not_iso_not_exists_mapPt_mapPt_mul_zpow_eq_zpow), where $k$ is chosen so that the shifted discriminant has the required shape.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mapPt_mapPt_mul_zpow_eq_zpow_sub_of_mapPt_mapPt_mul_zpow_eq_zpow.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_mapPt_mapPt_mul_zpow_eq_zpow_sub_of_mapPt_mapPt_mul_zpow_eq_zpow
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (t n k : ℤ)
    (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hadd : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver s E.f),
      mapPt φ hφ (E.L.mul s P Q) = E.L.mul s (mapPt φ hφ P) (mapPt φ hφ Q))
    (hlin : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x)
    (hrel : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ (mapPt φ hφ P) * P ^ n = mapPt φ hφ P ^ t) :
    ∃ (ψ : E.A ⟶ E.A) (hψ : ψ ≫ E.f = E.f),
      (∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver s E.f),
          mapPt ψ hψ (E.L.mul s P Q) = E.L.mul s (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ ψ = ψ ≫ E.act x) ∧
      (∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver s E.f),
          letI := E.L.pointCommGroup E.comm s
          mapPt ψ hψ P = mapPt φ hφ P * P ^ (-k)) ∧
      ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver s E.f),
        letI := E.L.pointCommGroup E.comm s
        mapPt ψ hψ (mapPt ψ hψ P) * P ^ (k ^ 2 - t * k + n) = mapPt ψ hψ P ^ (t - 2 * k) := by sorry
