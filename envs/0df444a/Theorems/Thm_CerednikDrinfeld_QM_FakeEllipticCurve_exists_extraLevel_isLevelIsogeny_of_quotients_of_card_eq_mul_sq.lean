-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/57024989-c55b-5b9d-9ae2-a9b399437c3b
-- title:
--   Level-ℓ isogeny between quotients of a Λ-stable filtration
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0<a$ or $0<b$, and for each height-one prime $v$ of $\mathcal O_{\mathbb Q}$ every nonzero element of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a unit exactly when $q$ or $q'$ lies in $v$. Let $\Lambda$ be a $\mathbb Z$-submodule that is an order maximal among orders, $E$ a fake elliptic curve over $\overline{\mathbb Q}$ for $\Lambda$ with level $N=1$, and $\ell$ a prime distinct from $q$ and $q'$. Let $H\subseteq H'$ be finite sets of $\overline{\mathbb Q}$-points of $E$ (sections of $E.f$ over the identity of $\operatorname{Spec}\overline{\mathbb Q}$) containing the identity and closed under the relative group law, its inverse and the pushforward by $E.\mathrm{act}\,x$ for every $x\in\Lambda$, with $\#H'=\ell^2\,\#H$ and $\ell P\in H$ for all $P\in H'$. Assume given quotient data $(C,p,K,\kappa)$ and $(C',p',K',\kappa')$: fake elliptic curves $C,C'$ of level $1$, morphisms $p:E.A\to C.A$, $p':E.A\to C'.A$ over $\overline{\mathbb Q}$ that are additive on $T$-points and commute with the $\Lambda$-actions, finite, flat, surjective and surjective on $\overline{\mathbb Q}$-points; closed immersions $\kappa,\kappa'$ from reduced schemes, finite over the base, whose $\overline{\mathbb Q}$-points factoring through them are exactly $H$, resp. $H'$, and which represent the kernels of $p$, resp. $p'$, on $T$-points for all $T$. Then there exists an extra level $Kx$ at $\ell$ on $C$ for which the pair $(C,Kx)$ is related to $C'$ by `IsLevelIsogeny ℓ`: there are mutually $\Lambda$-equivariant additive morphisms $\varphi:C.A\to C'.A$ and $\psi:C'.A\to C.A$ over the base whose two composites are the actions of $\ell$ (whenever $\ell\in\Lambda$), such that a $T$-point is killed by $\varphi$ exactly when it factors through the level subscheme of $Kx$, and $\varphi$ carries the level-one structure of $C$ into that of $C'$.
--
--   This is the step lemma for building chains of level-$\ell$ isogenies of fake elliptic curves: passing to the quotients by two $\Lambda$-stable subgroups $H\subseteq H'$ of index ratio $\ell^2$ with $\ell H'\subseteq H$ realises $C\to C'$ as a level-$\ell$ isogeny, the extra level being the image of $H'$. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_chain_of_filtration_mapPt_eq_one`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_chain_of_filtration_mapPt_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (E : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
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
    (hHH' : H ⊆ H') (hcard : Nat.card ↥H' = ℓ ^ 2 * Nat.card ↥H)
    (htors : ∀ P, P ∈ H' → nsmulPt E.L (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) ℓ P ∈ H)
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
    ∃ Kx : C.ExtraLevel ℓ,
      FakeEllipticCurve.IsLevelIsogeny ℓ (⟨C, Kx⟩ : FakeEllipticCurve.WithExtraLevel Λ 1 ℓ (AlgebraicClosure ℚ)) C' := by sorry
