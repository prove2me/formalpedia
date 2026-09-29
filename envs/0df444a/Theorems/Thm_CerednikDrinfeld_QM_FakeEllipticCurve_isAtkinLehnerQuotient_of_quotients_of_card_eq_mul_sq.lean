-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_quotients_of_card_eq_mul_sq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_quotients_of_card_eq_mul_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/ce8a80c4-35a7-50b4-9acf-fd9f5563f4a9
-- title:
--   Ramified step of a kernel filtration is an Atkin–Lehner quotient
-- statement:
--   Let $q\neq q'$ be primes and $a,b\in\mathbb{Q}$ with $a>0$ or $b>0$ such that for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra precisely when $v$ lies over $q$ or over $q'$; let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, and let $E$ be a fake elliptic curve of level $1$ for $\Lambda$ over $\overline{\mathbb{Q}}$ (a scheme $E.A$ with structure morphism $E.f$ to $\operatorname{Spec}\overline{\mathbb{Q}}$, a commutative relative group law $E.L$, smooth proper with connected fibres of dimension $2$, together with the $\Lambda$-action $E.act$). Let $r\in\{q,q'\}$. Let $H\subseteq H'$ be finite sets of $\overline{\mathbb{Q}}$-points of $E$ (sections of $E.f$ over the identity) each containing the unit, closed under the group law and inversion and stable under $E.act\,x$ for all $x\in\Lambda$, with $\#H'=r^2\cdot\#H$, and such that for every $P\in H'$ and every $m\in\Lambda$ whose reduced norm $m\,\overline{m}$ equals $rk$ for some $k\in\mathbb{Z}$ one has $E.act\,m\,(P)\in H$. Let $(C,p,K,\kappa)$ and $(C',p',K',\kappa')$ be quotient presentations of $E$ by $H$ and by $H'$ respectively: $C$ is a level-$1$ fake elliptic curve for $\Lambda$ over $\overline{\mathbb{Q}}$, $p:E.A\to C.A$ satisfies $p$ followed by $C.f$ equals $E.f$, is additive on $T$-points for every base morphism $t$, is $\Lambda$-equivariant ($E.act\,x$ followed by $p$ equals $p$ followed by $C.act\,x$), is finite, flat and surjective and surjective on $\overline{\mathbb{Q}}$-points, while $\kappa:K\to E.A$ is a closed immersion with $K$ reduced and $\kappa$ followed by $E.f$ finite, the $\overline{\mathbb{Q}}$-points factoring through $\kappa$ are exactly those in $H$, and for all $T$-points $Q$, $p\circ Q$ is the unit point iff $Q$ factors through $\kappa$ (the same conditions for $p'$, $\kappa'$ with $H'$ in place of $H$). The conclusion is `IsAtkinLehnerQuotient r C C'`: there are morphisms $\varphi:C.A\to C'.A$ and $\psi:C'.A\to C.A$ over $\operatorname{Spec}\overline{\mathbb{Q}}$, both additive on $T$-points and commuting with the $\Lambda$-actions, such that whenever $r\in\Lambda$ the composites are the actions of $r$ on $C$ and on $C'$, such that a $T$-point $P$ of $C$ satisfies $\varphi\circ P=$ unit exactly when $C.act\,m\,(P)$ is the unit point for every $m\in\Lambda$ with $m\,\overline{m}=rn$, $n\in\mathbb{Z}$, and such that $\varphi$ carries points factoring through $C.\mathrm{lev}$ to points factoring through $C'.\mathrm{lev}$.
--
--   This identifies the step map between two successive quotients of a fake elliptic curve by nested $\Lambda$-stable finite subgroups, in the ramified case $r\in\{q,q'\}$ with index $r^2$, as the Atkin–Lehner quotient at $r$: the descent of $p'$ through $p$ has kernel $C[\mathfrak{P}_r]$ and admits a dual whose composite with it is multiplication by $r$. It is used in the construction of chains of quotients along a $\Lambda$-stable kernel filtration, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_chain_of_filtration_mapPt_eq_one`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_chain_of_filtration_mapPt_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_quotients_of_card_eq_mul_sq.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_quotients_of_card_eq_mul_sq
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (E : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ))
    (r : ℕ) (hr : r = q ∨ r = q')
    (H : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f)) (hHfin : H.Finite)
    (hHone : E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ∈ H)
    (hHmul : ∀ P Q, P ∈ H → Q ∈ H → E.L.mul (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P Q ∈ H)
    (hHinv : ∀ P, P ∈ H → E.L.inv (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P ∈ H)
    (hHstab : ∀ (x : ↥Λ) P, P ∈ H → pushPt (E.act x) (E.act_over x) P ∈ H)
    (H' : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f)) (hH'fin : H'.Finite)
    (hH'one : E.L.one (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ∈ H')
    (hH'mul : ∀ P Q, P ∈ H' → Q ∈ H' → E.L.mul (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P Q ∈ H')
    (hH'inv : ∀ P, P ∈ H' → E.L.inv (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) P ∈ H')
    (hH'stab : ∀ (x : ↥Λ) P, P ∈ H' → pushPt (E.act x) (E.act_over x) P ∈ H')
    (hHH' : H ⊆ H') (hcard : Nat.card ↥H' = r ^ 2 * Nat.card ↥H)
    (hram : ∀ P, P ∈ H' → ∀ (m : ↥Λ) (k : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * k : ℚ) : ℍ[ℚ, a, b]) →
      pushPt (E.act m) (E.act_over m) P ∈ H)
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
    (C' : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ)) (p' : E.A ⟶ C'.A) (hp' : p' ≫ C'.f = E.f) (K' : Scheme.{0}) (κ' : K' ⟶ E.A)
    (hC' :
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
        mapPt p' hp' (E.L.mul t P Q) = C'.L.mul t (mapPt p' hp' P) (mapPt p' hp' Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ p' = p' ≫ C'.act x) ∧
      IsFinite p' ∧ Flat p' ∧ Surjective p' ∧
      (∀ R : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) C'.f, ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, mapPt p' hp' P = R) ∧
      IsClosedImmersion κ' ∧ IsReduced K' ∧ IsFinite (κ' ≫ E.f) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough κ' P ↔ P ∈ H') ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t E.f),
        mapPt p' hp' Q = C'.L.one t ↔ FactorsThrough κ' Q))
    :
    FakeEllipticCurve.IsAtkinLehnerQuotient r C C' := by sorry
