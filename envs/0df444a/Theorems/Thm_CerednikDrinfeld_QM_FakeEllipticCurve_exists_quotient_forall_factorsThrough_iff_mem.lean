-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_quotient_forall_factorsThrough_iff_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/9ecb6982-379f-5f33-bee8-2ee613267806
-- title:
--   Quotient of a level-one fake elliptic curve by H
-- statement:
--   Let $q,q'$ be primes with $q'\ne q$ and let $a,b\in\mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order (containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning, finitely generated) and maximal among orders, and let $E$ be a `FakeEllipticCurve Λ 1` over $\overline{\mathbb{Q}}$. Let $H$ be a finite set of sections of $E.f$ over the identity of $\operatorname{Spec}\overline{\mathbb{Q}}$ containing the unit section and stable under the group law, under inversion, and under composition with $E.\mathrm{act}\,x$ for every $x\in\Lambda$. Then there exist a `FakeEllipticCurve Λ 1` $C$ over $\overline{\mathbb{Q}}$, a morphism $p:E.A\to C.A$ with $p$ followed by $C.f$ equal to $E.f$, a scheme $K$ and $\kappa:K\to E.A$ such that: composition with $p$ is multiplicative on $T$-points for every $T$ and every $T\to\operatorname{Spec}\overline{\mathbb{Q}}$; $E.\mathrm{act}\,x$ followed by $p$ equals $p$ followed by $C.\mathrm{act}\,x$ for all $x\in\Lambda$; $p$ is finite, flat and surjective, and surjective on $\overline{\mathbb{Q}}$-sections; $\kappa$ is a closed immersion, $K$ is reduced, $\kappa$ followed by $E.f$ is finite; a $\overline{\mathbb{Q}}$-section of $E.f$ factors through $\kappa$ precisely when it lies in $H$; and for every $T$-point $Q$ of $E.f$, $Q$ followed by $p$ is the unit section of $C$ if and only if $Q$ factors through $\kappa$.
--
--   This is the construction of the quotient of a level-one fake elliptic curve by a finite $\Lambda$-stable subgroup of its $\overline{\mathbb{Q}}$-points, together with the reduced finite closed subscheme of $E$ cutting out the kernel functorially. It is used in the construction of chains of isogenies of fake elliptic curves along a filtration of a finite subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_forall_factorsThrough_iff_mem.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_quotient_forall_factorsThrough_iff_mem
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (E : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ))
    (H : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f)) (hHfin : H.Finite)
    (hHone : E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ∈ H)
    (hHmul : ∀ P Q, P ∈ H → Q ∈ H → E.L.mul (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P Q ∈ H)
    (hHinv : ∀ P, P ∈ H → E.L.inv (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P ∈ H)
    (hHstab : ∀ (x : ↥Λ) P, P ∈ H → pushPt (E.act x) (E.act_over x) P ∈ H)
    :
    ∃ (C : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ)) (p : E.A ⟶ C.A) (hp : p ≫ C.f = E.f) (K : Scheme.{0}) (κ : K ⟶ E.A),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
        mapPt p hp (E.L.mul t P Q) = C.L.mul t (mapPt p hp P) (mapPt p hp Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ p = p ≫ C.act x) ∧
      IsFinite p ∧ Flat p ∧ Surjective p ∧
      (∀ R : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) C.f, ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, mapPt p hp P = R) ∧
      IsClosedImmersion κ ∧ IsReduced K ∧ IsFinite (κ ≫ E.f) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough κ P ↔ P ∈ H) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t E.f),
        mapPt p hp Q = C.L.one t ↔ FactorsThrough κ Q) := by sorry
