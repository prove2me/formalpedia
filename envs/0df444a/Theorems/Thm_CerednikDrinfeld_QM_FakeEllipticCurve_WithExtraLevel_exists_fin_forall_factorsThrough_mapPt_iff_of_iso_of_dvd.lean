-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_fin_forall_factorsThrough_mapPt_iff_of_iso_of_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fin_forall_factorsThrough_mapPt_iff_of_iso_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/730b1b34-0149-5ff0-bc41-ff051e0ad9c4
-- title:
--   Isomorphic ℓ-level lifts pull back level-N structures alike
-- statement:
--   Fix primes $q\neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0<a$ or $0<b$ and, for every finite place $v$ of $\mathbb{Q}$, the completed algebra is a division algebra exactly when $v$ lies above $q$ or $q'$; fix a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ that is an order maximal among orders, an $N\neq 0$, and a prime $\ell\notin\{q,q'\}$ with $\ell\mid N$. The assertion is that there are an $m$ and a family $S:\mathrm{Fin}\,m\to$ `FakeEllipticCurve Λ N (AlgebraicClosure ℚ)` with the following property. Let $D$ be a fake elliptic curve over $\overline{\mathbb{Q}}$ isomorphic to no $S_j$, and let $u,u'$ be objects of `WithExtraLevel Λ N ℓ`, i.e. fake elliptic curves equipped with an `ExtraLevel ℓ` datum, with base-compatible morphisms $\varphi:u_1.A\to D.A$, $\psi:D.A\to u_1.A$ and $\varphi',\psi'$ for $u'$. Assume, for each leg, the six conditions: $\varphi$ and $\psi$ are homomorphisms for the relative group laws on $T$-points, both commute with the $\Lambda$-actions, $\psi\circ\varphi$ and $\varphi\circ\psi$ are multiplication by $\ell$, a $T$-point is killed by $\varphi$ exactly when it factors through the extra-level immersion `levK` of $u$, and $\varphi$ carries points factoring through `lev` of $u_1$ to points factoring through `lev` of $D$; likewise for $u',\varphi',\psi'$. If moreover $u$ and $u'$ are isomorphic in the sense of `WithExtraLevel.Iso`, then for every $\overline{\mathbb{Q}}$-point $P$ of $D$ (a section over the identity of $\mathrm{Spec}\,\overline{\mathbb{Q}}$), $\psi(P)$ factors through `lev` of $u_1$ if and only if $\psi'(P)$ factors through `lev` of $u'_1$. Note that the conclusion is claimed only on $\overline{\mathbb{Q}}$-points, not on all $T$-points.
--
--   This is the rigidity step used when comparing two lifts of a fake elliptic curve along an $\ell$-isogeny leg: off a finite list of exceptional isomorphism classes, an isomorphism of the two lifts induces an automorphism of the target that preserves the level-$N$ datum, so the two pulled-back level structures coincide. It feeds the count of lifts in the case $\ell\mid N$, being cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fin_isLevelIsogeny_iso_of_dvd`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fin_isLevelIsogeny_iso_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_fin_forall_factorsThrough_mapPt_iff_of_iso_of_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fin_forall_factorsThrough_mapPt_iff_of_iso_of_dvd
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') (hℓN : ℓ ∣ N)
    :
    ∃ (m : ℕ) (S : Fin m → FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
      ∀ (D : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)), (∀ j : Fin m, ¬ FakeEllipticCurve.Iso D (S j)) →
      ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ))
        (φ : u.1.A ⟶ D.A) (hφ : φ ≫ D.f = u.1.f) (ψ : D.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = D.f)
        (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ))
        (φ' : u'.1.A ⟶ D.A) (hφ' : φ' ≫ D.f = u'.1.f) (ψ' : D.A ⟶ u'.1.A) (hψ' : ψ' ≫ u'.1.f = D.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t u.1.f),
        mapPt φ hφ (u.1.L.mul t P Q) = D.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t D.f),
        mapPt ψ hψ (D.L.mul t P Q) = u.1.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) →
      (∀ x : ↥Λ, u.1.act x ≫ φ = φ ≫ D.act x) ∧ (∀ x : ↥Λ, D.act x ≫ ψ = ψ ≫ u.1.act x) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.1.f),
        mapPt ψ hψ (mapPt φ hφ P) = nsmulPt u.1.L t ℓ P) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t D.f),
        mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt D.L t ℓ Q) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.1.f),
        mapPt φ hφ P = D.L.one t ↔ FactorsThrough u.2.levK P) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u.1.f),
        FactorsThrough u.1.lev P → FactorsThrough D.lev (mapPt φ hφ P)) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t u'.1.f),
        mapPt φ' hφ' (u'.1.L.mul t P Q) = D.L.mul t (mapPt φ' hφ' P) (mapPt φ' hφ' Q)) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t D.f),
        mapPt ψ' hψ' (D.L.mul t P Q) = u'.1.L.mul t (mapPt ψ' hψ' P) (mapPt ψ' hψ' Q)) →
      (∀ x : ↥Λ, u'.1.act x ≫ φ' = φ' ≫ D.act x) ∧ (∀ x : ↥Λ, D.act x ≫ ψ' = ψ' ≫ u'.1.act x) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u'.1.f),
        mapPt ψ' hψ' (mapPt φ' hφ' P) = nsmulPt u'.1.L t ℓ P) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t D.f),
        mapPt φ' hφ' (mapPt ψ' hψ' Q) = nsmulPt D.L t ℓ Q) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u'.1.f),
        mapPt φ' hφ' P = D.L.one t ↔ FactorsThrough u'.2.levK P) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u'.1.f),
        FactorsThrough u'.1.lev P → FactorsThrough D.lev (mapPt φ' hφ' P)) →
      FakeEllipticCurve.WithExtraLevel.Iso u u' →
        ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f, FactorsThrough u.1.lev (mapPt ψ hψ P) ↔ FactorsThrough u'.1.lev (mapPt ψ' hψ' P) := by sorry
