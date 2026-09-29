-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/45118cf5-076e-5e05-af5c-f787ac3712ad
-- title:
--   Base change of an extra level and a level-ℓ isogeny
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, commutative rings $S,S'$, a ring homomorphism $\varphi : S \to S'$ and a natural number $\ell$. Let $u = (u_1, u_2)$ consist of a fake elliptic curve $u_1$ over $S$ together with an extra level $u_2$ at $\ell$ on it (a closed immersion $\mathrm{levK} : K \to u_1.A$ whose $T$-points form a subgroup killed by $\ell$, stable under the $\Lambda$-action, meeting the points of $u_1.\mathrm{lev}$ only in the identity, with $\mathrm{levK}$ followed by $u_1.f$ finite, flat, locally of finite presentation of fibre rank $\ell^2$, and geometric fibres isomorphic as groups to $\mathbb{Z}/\ell \times \mathbb{Z}/\ell$ whenever $\ell$ is invertible), let $\mathcal{D}$ be a fake elliptic curve over $S$, and assume `IsLevelIsogeny ℓ u 𝒟`: there are morphisms $\alpha : u_1.A \to \mathcal{D}.A$ and $\beta : \mathcal{D}.A \to u_1.A$ over $S$, each additive on $T$-points and commuting with the $\Lambda$-actions, whose composites are the actions of $\ell$ in either order whenever $\ell \in \Lambda$, with $\alpha$ killing exactly the points factoring through $u_2.\mathrm{levK}$ and carrying $u_1.\mathrm{lev}$-points to $\mathcal{D}.\mathrm{lev}$-points. Let $\bar A$ and $\bar D$ be fake elliptic curves over $S'$, given together with morphisms $g : \bar A.A \to u_1.A$ and $h : \bar D.A \to \mathcal{D}.A$ such that the squares formed by $g$, $\bar A.f$, $u_1.f$ and $\mathrm{Spec}\,\varphi$, respectively by $h$, $\bar D.f$, $\mathcal{D}.f$ and $\mathrm{Spec}\,\varphi$, are cartesian, such that $g$ and $h$ are additive on points over $S'$ (the product of two points composed with $g$, resp. $h$, is the product of their composites, taken over the corresponding base point over $S$), such that $\bar A.\mathrm{act}\,x$ followed by $g$ equals $g$ followed by $u_1.\mathrm{act}\,x$ and likewise for $h$, and such that a point $P$ over $S'$ factors through $\bar A.\mathrm{lev}$ if and only if $P$ followed by $g$ factors through $u_1.\mathrm{lev}$, and correspondingly for $\bar D.\mathrm{lev}$, $h$ and $\mathcal{D}.\mathrm{lev}$ (both implications being hypotheses). The conclusion is that there exists an extra level $\bar K$ at $\ell$ on $\bar A$ whose points are characterised by $g$, namely a point $P$ over $S'$ factors through $\bar K.\mathrm{levK}$ if and only if $P$ followed by $g$ factors through $u_2.\mathrm{levK}$, and such that $\bar D$ is a level-$\ell$ isogeny quotient of $(\bar A, \bar K)$ in the above sense.
--
--   This is the base-change statement for the moduli problem of fake elliptic curves with extra level at $\ell$: pulling back along a ring map $S \to S'$ carries an extra level and its $\ell$-isogeny quotient to an extra level and its $\ell$-isogeny quotient, with the pulled-back level described by its points. It is used in the construction of the level tower and in the computation of the Frobenius correspondence on the integral model of the Shimura curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM
open scoped Quaternion

open CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') (ℓ : ℕ)
    (u : WithExtraLevel Λ N ℓ S) (𝒟 : FakeEllipticCurve Λ N S) (hud : IsLevelIsogeny ℓ u 𝒟)
    (Ā Dbar : FakeEllipticCurve Λ N S')

    (g : Ā.A ⟶ u.1.A) (hg : CategoryTheory.IsPullback g Ā.f u.1.f (Spec.map (CommRingCat.ofHom φ)))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' Ā.f),
      (Ā.L.mul t' P Q).1 ≫ g =
        (u.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hg_act : ∀ x : ↥Λ, Ā.act x ≫ g = g ≫ u.1.act x)
    (hg_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Ā.f),
      FactorsThrough Ā.lev P → ∃ P₀ : T ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g)
    (hg_lev' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Ā.f),
      (∃ P₀ : T ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g) → FactorsThrough Ā.lev P)

    (h : Dbar.A ⟶ 𝒟.A) (hh : CategoryTheory.IsPullback h Dbar.f 𝒟.f (Spec.map (CommRingCat.ofHom φ)))
    (hh_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' Dbar.f),
      (Dbar.L.mul t' P Q).1 ≫ h =
        (𝒟.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, Q.2]⟩).1)
    (hh_act : ∀ x : ↥Λ, Dbar.act x ≫ h = h ≫ 𝒟.act x)
    (hh_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Dbar.f),
      FactorsThrough Dbar.lev P → ∃ P₀ : T ⟶ 𝒟.C, P₀ ≫ 𝒟.lev = P.1 ≫ h)
    (hh_lev' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Dbar.f),
      (∃ P₀ : T ⟶ 𝒟.C, P₀ ≫ 𝒟.lev = P.1 ≫ h) → FactorsThrough Dbar.lev P) :
    ∃ Kbar : Ā.ExtraLevel ℓ,

      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Ā.f),
          FactorsThrough Kbar.levK P ↔ ∃ P₀ : T ⟶ u.2.K, P₀ ≫ u.2.levK = P.1 ≫ g) ∧
      IsLevelIsogeny ℓ (⟨Ā, Kbar⟩ : WithExtraLevel Λ N ℓ S') Dbar := by sorry
