-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_levelExt_setOf_factorsThrough_mapPt_of_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.levelExt_setOf_factorsThrough_mapPt_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/c3de4cb6-3949-52d1-a2bd-9a4fc8a389b1
-- title:
--   ψ-preimage of the level structure is a level-Nℓ extension
-- statement:
--   Fix primes $q\neq q'$ and rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completed algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$; let $\Lambda$ be a $\mathbb Z$-submodule which is an order maximal among orders, $N\neq 0$, and $\ell$ a prime with $\ell\neq q,q'$ and $\ell\mid N$. Let $D$ be a fake elliptic curve of level $N$ for $\Lambda$ over $\overline{\mathbb Q}$, and $u=(E,K)$ such a curve $E=u.1$ together with an extra level structure $u.2$ of level $\ell$. Let $\varphi:E\to D$ and $\psi:D\to E$ be morphisms over $\operatorname{Spec}\overline{\mathbb Q}$ which, on points over every test scheme, are homomorphisms for the relative group laws, commute with the $\Lambda$-actions, satisfy $\psi\circ\varphi=[\ell]$ on $E$ and $\varphi\circ\psi=[\ell]$ on $D$, have $\varphi(P)$ the identity point precisely when $P$ factors through `u.2.levK`, and carry points factoring through `E.lev` to points factoring through `D.lev`. Then the set $S$ of $\overline{\mathbb Q}$-points $P$ of $D$ (sections of `D.f` over the identity of $\operatorname{Spec}\overline{\mathbb Q}$) with $\psi(P)$ factoring through `E.lev` satisfies the six clauses: $S$ is closed under the group law and inversion; it contains the identity point; it is stable under each $\Lambda$-action `D.act x`; $\ell P$ factors through `D.lev` for $P\in S$; every point factoring through `D.lev` equals $\ell P$ for some $P\in S$; and any $P\in S$ with $\ell P$ the identity factors through `D.lev`.
--
--   This says that the $\psi$-preimage of the level-$N$ structure of $E$ is a level-$N\ell$ extension of the level structure of $D$, stated as the explicit six-clause conjunction rather than as a packaged predicate. It is used in the count of lifts of $D$ along $\ell$-isogenies, in [`CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fin_isLevelIsogeny_iso_of_dvd`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fin_isLevelIsogeny_iso_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_levelExt_setOf_factorsThrough_mapPt_of_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.levelExt_setOf_factorsThrough_mapPt_of_dvd
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') (hℓN : ℓ ∣ N)
    (D : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ))
    (φ : u.1.A ⟶ D.A) (hφ : φ ≫ D.f = u.1.f) (ψ : D.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = D.f)
    (φ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t u.1.f),
      mapPt φ hφ (u.1.L.mul t P Q) = D.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (ψ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t D.f),
      mapPt ψ hψ (D.L.mul t P Q) = u.1.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (φ_act : ∀ x : ↥Λ, u.1.act x ≫ φ = φ ≫ D.act x) (ψ_act : ∀ x : ↥Λ, D.act x ≫ ψ = ψ ≫ u.1.act x)
    (hψφ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.1.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt u.1.L t ℓ P)
    (hφψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t D.f),
      mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt D.L t ℓ Q)
    (hkerφ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.1.f),
      mapPt φ hφ P = D.L.one t ↔ FactorsThrough u.2.levK P)
    (φ_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P → FactorsThrough D.lev (mapPt φ hφ P))
    :
    (∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f, P ∈ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f | FactorsThrough u.1.lev (mapPt ψ hψ P)} → Q ∈ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f | FactorsThrough u.1.lev (mapPt ψ hψ P)} → D.L.mul _ P Q ∈ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f | FactorsThrough u.1.lev (mapPt ψ hψ P)} ∧ D.L.inv _ P ∈ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f | FactorsThrough u.1.lev (mapPt ψ hψ P)}) ∧
      D.L.one _ ∈ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f | FactorsThrough u.1.lev (mapPt ψ hψ P)} ∧
      (∀ (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f), P ∈ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f | FactorsThrough u.1.lev (mapPt ψ hψ P)} → pushPt (D.act x) (D.act_over x) P ∈ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f | FactorsThrough u.1.lev (mapPt ψ hψ P)}) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f, P ∈ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f | FactorsThrough u.1.lev (mapPt ψ hψ P)} → FactorsThrough D.lev (nsmulPt D.L _ ℓ P)) ∧
      (∀ Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f, FactorsThrough D.lev Q → ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f, P ∈ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f | FactorsThrough u.1.lev (mapPt ψ hψ P)} ∧ nsmulPt D.L _ ℓ P = Q) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f, P ∈ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f | FactorsThrough u.1.lev (mapPt ψ hψ P)} → nsmulPt D.L _ ℓ P = D.L.one _ → FactorsThrough D.lev P) := by sorry
