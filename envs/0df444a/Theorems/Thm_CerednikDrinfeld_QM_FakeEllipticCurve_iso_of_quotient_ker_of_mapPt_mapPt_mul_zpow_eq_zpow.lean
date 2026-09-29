-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_quotient_ker_of_mapPt_mapPt_mul_zpow_eq_zpow
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_quotient_ker_of_mapPt_mapPt_mul_zpow_eq_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/8a23ef45-536f-5e8b-83df-cf63048d8469
-- title:
--   Quotient by the kernel of an endomorphism is isomorphic to E
-- statement:
--   Let $q\neq q'$ be primes and $a,b\in\mathbb{Q}$ with `IsIndefiniteRamifiedExactlyAt a b q q'`: either $a>0$ or $b>0$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, and let $E$ be a fake elliptic curve over $\overline{\mathbb{Q}}$ of level $N=1$ for $\Lambda$. Let $t,n\in\mathbb{Z}$ with $t^2<4n$, and let $\varphi\colon E.A\to E.A$ satisfy $\varphi\circ E.f=E.f$, be additive on $T$-points for the relative group law of $E$ for every test scheme $T$ over $\operatorname{Spec}\overline{\mathbb{Q}}$, commute with $E.\mathrm{act}\,x$ for all $x\in\Lambda$, and satisfy $\varphi(\varphi(P))\cdot P^{\,n}=\varphi(P)^{\,t}$ in the commutative group of $T$-points, for all $T$-points $P$. Let $H$ be a finite set of $\overline{\mathbb{Q}}$-points of $E$ (sections over the identity of $\operatorname{Spec}\overline{\mathbb{Q}}$) containing the unit, closed under the group law and inversion, stable under push-forward by each $E.\mathrm{act}\,x$, and equal to the set of $P$ with $\varphi(P)=1$. Let $C$ be a further level-one fake elliptic curve for $\Lambda$ over $\overline{\mathbb{Q}}$, let $p\colon E.A\to C.A$ satisfy $p\circ C.f=E.f$, and let $\kappa\colon K\to E.A$ be a morphism from a scheme $K$, subject to the conjunction `hC`: $p$ is additive on $T$-points, commutes with the $\Lambda$-actions, is finite, flat and surjective, is onto on $\overline{\mathbb{Q}}$-points, $\kappa$ is a closed immersion with $K$ reduced and $\kappa$ followed by $E.f$ finite, a $\overline{\mathbb{Q}}$-point of $E$ factors through $\kappa$ precisely when it lies in $H$, and a $T$-point $Q$ satisfies $p\circ Q=1$ precisely when $Q$ factors through $\kappa$. The conclusion is `FakeEllipticCurve.Iso C E`: there is an isomorphism $e\colon C.A\cong E.A$ with $e$ followed by $E.f$ equal to $C.f$, compatible with the group laws on $T$-points, intertwining the $\Lambda$-actions, and such that a $T$-point of $C$ factors through $C.\mathrm{lev}$ iff its image under $e$ factors through $E.\mathrm{lev}$.
--
--   This identifies the quotient of a level-one fake elliptic curve by the kernel of a $\Lambda$-linear endomorphism satisfying $\varphi^2-t\varphi+n=0$ with $t^2<4n$, presented via a finite flat surjection $p$ and a reduced finite closed subscheme cutting out the kernel, with $E$ itself, as level-one fake elliptic curves. It is used in the construction of chains of such curves attached to a filtration of kernels of iterates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_quotient_ker_of_mapPt_mapPt_mul_zpow_eq_zpow.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_quotient_ker_of_mapPt_mapPt_mul_zpow_eq_zpow
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (E : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ))
    (t n : ℤ) (htn : t ^ 2 < 4 * n)
    (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f)
    (hadd : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver s E.f),
      mapPt φ hφ (E.L.mul s P Q) = E.L.mul s (mapPt φ hφ P) (mapPt φ hφ Q))
    (hlin : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x)
    (hrel : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver s E.f),
      letI := E.L.pointCommGroup E.comm s
      mapPt φ hφ (mapPt φ hφ P) * P ^ n = mapPt φ hφ P ^ t)
    (H : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f)) (hHfin : H.Finite)
    (hHone : E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ∈ H)
    (hHmul : ∀ P Q, P ∈ H → Q ∈ H → E.L.mul (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P Q ∈ H)
    (hHinv : ∀ P, P ∈ H → E.L.inv (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P ∈ H)
    (hHstab : ∀ (x : ↥Λ) P, P ∈ H → pushPt (E.act x) (E.act_over x) P ∈ H)
    (hHφ : ∀ P, P ∈ H ↔ mapPt φ hφ P = E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))))
    (C : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ)) (p : E.A ⟶ C.A) (hp : p ≫ C.f = E.f) (K : Scheme.{0}) (κ : K ⟶ E.A)
    (hC :
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
        mapPt p hp (E.L.mul t P Q) = C.L.mul t (mapPt p hp P) (mapPt p hp Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ p = p ≫ C.act x) ∧
      IsFinite p ∧ Flat p ∧ Surjective p ∧
      (∀ R : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) C.f, ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, mapPt p hp P = R) ∧
      IsClosedImmersion κ ∧ IsReduced K ∧ IsFinite (κ ≫ E.f) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough κ P ↔ P ∈ H) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t E.f),
        mapPt p hp Q = C.L.one t ↔ FactorsThrough κ Q))
    :
    FakeEllipticCurve.Iso C E := by sorry
