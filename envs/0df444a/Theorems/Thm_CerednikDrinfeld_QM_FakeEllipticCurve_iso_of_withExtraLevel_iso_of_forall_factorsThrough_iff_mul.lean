-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_withExtraLevel_iso_of_forall_factorsThrough_iff_mul
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_withExtraLevel_iso_of_forall_factorsThrough_iff_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/2bb6c1b7-d0f8-5d48-a349-2cd9efe52b95
-- title:
--   Isomorphic (N,ℓ)-pairs yield isomorphic level-Nℓ curves
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N,\ell$ with $\gcd(N,\ell)=1$, and a commutative ring $S$. Let $u_1,u_2$ be fake elliptic curves over $S$ of level $N$ with $\Lambda$-action, each equipped with an extra level structure at $\ell$ (a closed subscheme $K$ of the total space, given by `levK`), and suppose $u_1$ and $u_2$ are isomorphic as such pairs: there is an isomorphism of the underlying schemes over $\mathrm{Spec}\,S$ which is additive for the relative group laws on $T$-points, commutes with the $\Lambda$-action, and matches both the `lev`- and the `levK`-subschemes in the sense that a $T$-point factors through one exactly when its image factors through the other. Let furthermore $E_1,E_2$ be fake elliptic curves over $S$ of level $N\ell$, and for $i=1,2$ let $e_i:u_i.1.A\cong E_i.A$ be an isomorphism over $\mathrm{Spec}\,S$ (i.e. $e_i$ followed by $E_i.f$ equals $u_i.1.f$) which is additive on $T$-points and intertwines the two $\Lambda$-actions, and assume that for every scheme $T$ over $\mathrm{Spec}\,S$ and every $T$-point $P$ of $u_i.1$: $P$ factors through $u_i.1.\mathrm{lev}$ iff $e_i(P)$ factors through $E_i.\mathrm{lev}$ and $N\cdot e_i(P)$ is the identity section, and $P$ factors through $u_i.2.\mathrm{levK}$ iff $e_i(P)$ factors through $E_i.\mathrm{lev}$ and $\ell\cdot e_i(P)$ is the identity section. Then $E_1$ and $E_2$ are isomorphic as fake elliptic curves of level $N\ell$, i.e. there is an isomorphism of their total spaces over $\mathrm{Spec}\,S$, additive on $T$-points, commuting with the $\Lambda$-action, and identifying the `lev`-subschemes on $T$-points.
--
--   This is the statement that the passage from a pair (level-$N$ structure, extra level structure at $\ell$) to a single level-$N\ell$ structure respects isomorphisms, the coprimality of $N$ and $\ell$ being what allows a point of the level-$N\ell$ structure to be split into its $N$-part and its $\ell$-part. It feeds the comparison of coarse moduli data at levels $(N,\ell)$ and $N\ell$ used in [`CerednikDrinfeld.QM.IsCoarseModuliT.exists_isCoarseModuli_mul_of_coprime_of_isUnit`](thm.html#CerednikDrinfeld.QM.IsCoarseModuliT.exists_isCoarseModuli_mul_of_coprime_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_withExtraLevel_iso_of_forall_factorsThrough_iff_mul.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_withExtraLevel_iso_of_forall_factorsThrough_iff_mul
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} (hNℓ : N.Coprime ℓ) {S : Type} [CommRing S]
    (u₁ u₂ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (h : FakeEllipticCurve.WithExtraLevel.Iso u₁ u₂)
    (E₁ : FakeEllipticCurve Λ (N * ℓ) S)
    (e₁ : u₁.1.A ≅ E₁.A) (he₁ : e₁.hom ≫ E₁.f = u₁.1.f)
    (e₁_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u₁.1.f),
      mapPt e₁.hom he₁ (u₁.1.L.mul t P Q) = E₁.L.mul t (mapPt e₁.hom he₁ P) (mapPt e₁.hom he₁ Q))
    (e₁_act : ∀ x : ↥Λ, u₁.1.act x ≫ e₁.hom = e₁.hom ≫ E₁.act x)
    (e₁_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₁.1.f),
      FactorsThrough u₁.1.lev P ↔
        FactorsThrough E₁.lev (mapPt e₁.hom he₁ P) ∧ nsmulPt E₁.L t N (mapPt e₁.hom he₁ P) = E₁.L.one t)
    (e₁_levK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₁.1.f),
      FactorsThrough u₁.2.levK P ↔
        FactorsThrough E₁.lev (mapPt e₁.hom he₁ P) ∧ nsmulPt E₁.L t ℓ (mapPt e₁.hom he₁ P) = E₁.L.one t)
    (E₂ : FakeEllipticCurve Λ (N * ℓ) S)
    (e₂ : u₂.1.A ≅ E₂.A) (he₂ : e₂.hom ≫ E₂.f = u₂.1.f)
    (e₂_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u₂.1.f),
      mapPt e₂.hom he₂ (u₂.1.L.mul t P Q) = E₂.L.mul t (mapPt e₂.hom he₂ P) (mapPt e₂.hom he₂ Q))
    (e₂_act : ∀ x : ↥Λ, u₂.1.act x ≫ e₂.hom = e₂.hom ≫ E₂.act x)
    (e₂_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₂.1.f),
      FactorsThrough u₂.1.lev P ↔
        FactorsThrough E₂.lev (mapPt e₂.hom he₂ P) ∧ nsmulPt E₂.L t N (mapPt e₂.hom he₂ P) = E₂.L.one t)
    (e₂_levK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u₂.1.f),
      FactorsThrough u₂.2.levK P ↔
        FactorsThrough E₂.lev (mapPt e₂.hom he₂ P) ∧ nsmulPt E₂.L t ℓ (mapPt e₂.hom he₂ P) = E₂.L.one t) :
    FakeEllipticCurve.Iso E₁ E₂ := by sorry
