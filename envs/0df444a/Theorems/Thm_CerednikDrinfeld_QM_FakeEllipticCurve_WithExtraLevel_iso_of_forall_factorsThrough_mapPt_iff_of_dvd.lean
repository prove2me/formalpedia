-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_forall_factorsThrough_mapPt_iff_of_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_forall_factorsThrough_mapPt_iff_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/d79e2bb7-8440-5781-a99e-9c735915d3ee
-- title:
--   Lifts of D with the same pulled-back level structure agree
-- statement:
--   Let $q\neq q'$ be primes, let $a,b\in\mathbb Q$ be such that $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0<a$ or $0<b$ and, for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$, every nonzero element of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a unit exactly when $v$ contains $q$ or $q'$; let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is an order maximal among orders, $N\neq 0$, and $\ell$ a prime with $\ell\neq q,q'$ and $\ell\mid N$. Let $D$ be a fake elliptic curve of level $N$ over $\overline{\mathbb Q}$ and let $u=(E,K)$, $u'=(E',K')$ be fake elliptic curves of level $N$ with an extra level structure of order $\ell$. Assume given $\varphi:E\to D$, $\psi:D\to E$ over $\operatorname{Spec}\overline{\mathbb Q}$ which, on $T$-points for all $T$ over the base, are homomorphisms for the relative group laws, commute with the $\Lambda$-actions, satisfy $\psi\varphi=[\ell]$ and $\varphi\psi=[\ell]$, have the property that $\varphi\circ P$ is the identity section precisely when $P$ factors through the extra-level map `u.2.levK`, and carry points factoring through `u.1.lev` to points factoring through `D.lev`; and likewise for $\varphi',\psi'$ and $u'$. Assume finally that for every $\overline{\mathbb Q}$-point $P$ of $D$, $\psi\circ P$ factors through `u.1.lev` if and only if $\psi'\circ P$ factors through `u'.1.lev`. Then $u$ and $u'$ are isomorphic: there is an isomorphism $E\cong E'$ over the base compatible with the group laws on all $T$-points, with the $\Lambda$-actions, and matching the loci of points factoring through `lev` and through `levK`.
--
--   This is the uniqueness half of the description of the fibres of the forgetful map from level-$N\ell$ to level-$N$ data on fake elliptic curves: two $\ell$-isogeny lifts of the same $D$ that pull the level-$N$ structure back to the same subgroup of $D(\overline{\mathbb Q})$ are isomorphic. It is used in the count of such lifts, [`CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fin_isLevelIsogeny_iso_of_dvd`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fin_isLevelIsogeny_iso_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_forall_factorsThrough_mapPt_iff_of_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_forall_factorsThrough_mapPt_iff_of_dvd
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') (hℓN : ℓ ∣ N)
    (D : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ))
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
    (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ))
    (φ' : u'.1.A ⟶ D.A) (hφ' : φ' ≫ D.f = u'.1.f) (ψ' : D.A ⟶ u'.1.A) (hψ' : ψ' ≫ u'.1.f = D.f)
    (φ'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t u'.1.f),
      mapPt φ' hφ' (u'.1.L.mul t P Q) = D.L.mul t (mapPt φ' hφ' P) (mapPt φ' hφ' Q))
    (ψ'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t D.f),
      mapPt ψ' hψ' (D.L.mul t P Q) = u'.1.L.mul t (mapPt ψ' hψ' P) (mapPt ψ' hψ' Q))
    (φ'_act : ∀ x : ↥Λ, u'.1.act x ≫ φ' = φ' ≫ D.act x) (ψ'_act : ∀ x : ↥Λ, D.act x ≫ ψ' = ψ' ≫ u'.1.act x)
    (hψ'φ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u'.1.f),
      mapPt ψ' hψ' (mapPt φ' hφ' P) = nsmulPt u'.1.L t ℓ P)
    (hφ'ψ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t D.f),
      mapPt φ' hφ' (mapPt ψ' hψ' Q) = nsmulPt D.L t ℓ Q)
    (hkerφ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u'.1.f),
      mapPt φ' hφ' P = D.L.one t ↔ FactorsThrough u'.2.levK P)
    (φ'_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t u'.1.f),
      FactorsThrough u'.1.lev P → FactorsThrough D.lev (mapPt φ' hφ' P))
    (h : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) D.f, FactorsThrough u.1.lev (mapPt ψ hψ P) ↔ FactorsThrough u'.1.lev (mapPt ψ' hψ' P)) :
    FakeEllipticCurve.WithExtraLevel.Iso u u' := by sorry
