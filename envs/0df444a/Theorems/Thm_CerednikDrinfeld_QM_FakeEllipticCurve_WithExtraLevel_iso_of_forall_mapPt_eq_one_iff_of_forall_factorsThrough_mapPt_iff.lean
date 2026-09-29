-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_forall_mapPt_eq_one_iff_of_forall_factorsThrough_mapPt_iff
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_forall_mapPt_eq_one_iff_of_forall_factorsThrough_mapPt_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/0faa799e-b632-51e5-97f2-fa6331ba77da
-- title:
--   Uniqueness of the source of an ℓ-isogeny onto a fake elliptic curve
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order (it contains $1$, is closed under multiplication, spans the quaternion algebra over $\mathbb{Q}$, and is finitely generated); let $N$ be a nonzero natural number, $\ell$ a prime, and $k$ an algebraically closed field in which both $\ell$ and $N$ are nonzero. Let $D$ be a fake elliptic curve over $k$ of level $N$ for $\Lambda$, and let $u=(E,K)$ and $u'=(E',K')$ be fake elliptic curves over $k$ each equipped with an extra level structure at $\ell$. Assume given morphisms $\varphi\colon E.A\to D.A$ and $\psi\colon D.A\to E.A$ over $\operatorname{Spec}k$ such that, on $T$-points over $\operatorname{Spec}k$ for every scheme $T$, composition with $\varphi$ and with $\psi$ is a homomorphism for the relative group laws, that $\varphi$ and $\psi$ commute with the $\Lambda$-actions ($E.\mathrm{act}(x)$ followed by $\varphi$ equals $\varphi$ followed by $D.\mathrm{act}(x)$, and symmetrically for $\psi$), that the two composites are the $\ell$-fold iterate of the group law (`nsmulPt` at $\ell$) on $T$-points of $E$ and of $D$ respectively, that a $T$-point $P$ of $E$ satisfies $\varphi\circ P=$ the identity section of $D$ exactly when $P$ factors through $K.\mathrm{levK}$, and that $\varphi$ carries $T$-points factoring through $E.\mathrm{lev}$ to $T$-points factoring through $D.\mathrm{lev}$; assume the same data $(\varphi',\psi')$ for $u'$. Assume finally that for every $k$-point $P$ of $D$ (a section over the identity of $\operatorname{Spec}k$): $\psi\circ P$ is the identity section of $E$ if and only if $\psi'\circ P$ is the identity section of $E'$, and $\psi\circ P$ factors through $E.\mathrm{lev}$ if and only if $\psi'\circ P$ factors through $E'.\mathrm{lev}$. Then $u$ and $u'$ are isomorphic as fake elliptic curves with extra level $\ell$: there is an isomorphism $e\colon E.A\cong E'.A$ over $\operatorname{Spec}k$ which is a homomorphism for the group laws on all $T$-points, commutes with the $\Lambda$-actions, and for which a $T$-point of $E$ factors through $E.\mathrm{lev}$ (respectively $K.\mathrm{levK}$) precisely when its image under $e$ factors through $E'.\mathrm{lev}$ (respectively $K'.\mathrm{levK}$).
--
--   This is the uniqueness statement for the source of an $\ell$-isogeny onto a fixed fake elliptic curve: the source, together with its level-$N$ and extra level-$\ell$ data, is determined up to isomorphism by the kernel of the dual isogeny on $k$-points and by the preimage of the level structure. It is used in the enumeration of the $\ell$-isogenies with given target, through [`CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fin_forall_isLevelIsogeny_iso`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fin_forall_isLevelIsogeny_iso) and [`CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_forall_factorsThrough_mapPt_iff_of_dvd`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_forall_factorsThrough_mapPt_iff_of_dvd), in the Čerednik–Drinfeld description of quaternionic moduli.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_forall_mapPt_eq_one_iff_of_forall_factorsThrough_mapPt_iff.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_forall_mapPt_eq_one_iff_of_forall_factorsThrough_mapPt_iff
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0) (hNk : (N : k) ≠ 0)
    (D : FakeEllipticCurve Λ N k)
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k)
    (φ : u.1.A ⟶ D.A) (hφ : φ ≫ D.f = u.1.f) (ψ : D.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = D.f)
    (φ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t u.1.f),
      mapPt φ hφ (u.1.L.mul t P Q) = D.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (ψ_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t D.f),
      mapPt ψ hψ (D.L.mul t P Q) = u.1.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (φ_act : ∀ x : ↥Λ, u.1.act x ≫ φ = φ ≫ D.act x) (ψ_act : ∀ x : ↥Λ, D.act x ≫ ψ = ψ ≫ u.1.act x)
    (hψφ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      mapPt ψ hψ (mapPt φ hφ P) = nsmulPt u.1.L t ℓ P)
    (hφψ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t D.f),
      mapPt φ hφ (mapPt ψ hψ Q) = nsmulPt D.L t ℓ Q)
    (hkerφ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      mapPt φ hφ P = D.L.one t ↔ FactorsThrough u.2.levK P)
    (φ_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P → FactorsThrough D.lev (mapPt φ hφ P))
    (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ k)
    (φ' : u'.1.A ⟶ D.A) (hφ' : φ' ≫ D.f = u'.1.f) (ψ' : D.A ⟶ u'.1.A) (hψ' : ψ' ≫ u'.1.f = D.f)
    (φ'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t u'.1.f),
      mapPt φ' hφ' (u'.1.L.mul t P Q) = D.L.mul t (mapPt φ' hφ' P) (mapPt φ' hφ' Q))
    (ψ'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t D.f),
      mapPt ψ' hψ' (D.L.mul t P Q) = u'.1.L.mul t (mapPt ψ' hψ' P) (mapPt ψ' hψ' Q))
    (φ'_act : ∀ x : ↥Λ, u'.1.act x ≫ φ' = φ' ≫ D.act x) (ψ'_act : ∀ x : ↥Λ, D.act x ≫ ψ' = ψ' ≫ u'.1.act x)
    (hψ'φ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u'.1.f),
      mapPt ψ' hψ' (mapPt φ' hφ' P) = nsmulPt u'.1.L t ℓ P)
    (hφ'ψ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t D.f),
      mapPt φ' hφ' (mapPt ψ' hψ' Q) = nsmulPt D.L t ℓ Q)
    (hkerφ' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u'.1.f),
      mapPt φ' hφ' P = D.L.one t ↔ FactorsThrough u'.2.levK P)
    (φ'_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t u'.1.f),
      FactorsThrough u'.1.lev P → FactorsThrough D.lev (mapPt φ' hφ' P))
    (hker : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.f, mapPt ψ hψ P = u.1.L.one _ ↔ mapPt ψ' hψ' P = u'.1.L.one _)
    (h : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.f, FactorsThrough u.1.lev (mapPt ψ hψ P) ↔ FactorsThrough u'.1.lev (mapPt ψ' hψ' P)) :
    FakeEllipticCurve.WithExtraLevel.Iso u u' := by sorry
