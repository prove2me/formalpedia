-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_iso_of_forall_factorsThrough_iff_mul
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_iso_of_forall_factorsThrough_iff_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/eb8b7702-0612-517c-83ef-cc3abe2e7425
-- title:
--   Isomorphisms transport splittings of level Nℓ structures
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N,\ell$ and a commutative ring $S$. Let $E_1,E_2$ be fake elliptic curves over $S$ with $\Lambda$-action and level structure of level $N\ell$, and assume `FakeEllipticCurve.Iso E₁ E₂`: there is an isomorphism of their total spaces over $\operatorname{Spec} S$ which is a homomorphism for the relative group laws on $T$-points for every $S$-scheme $T$, commutes with the $\Lambda$-action, and matches the two level subschemes in the sense that a $T$-point factors through $E_1.\mathrm{lev}$ exactly when its image factors through $E_2.\mathrm{lev}$. Let $u_1,u_2$ be pairs consisting of a fake elliptic curve of level $N$ over $S$ together with an extra level structure at $\ell$ (a closed subscheme $K$ with its structural axioms). Assume for $i=1,2$ an isomorphism $e_i : u_i.1.A \cong E_i.A$ over $\operatorname{Spec} S$ which is a homomorphism on $T$-points, commutes with the $\Lambda$-action, and such that, for every $S$-scheme $T$ and every $T$-point $P$ of $u_i.1$: $P$ factors through $u_i.1.\mathrm{lev}$ iff its image under $e_i$ factors through $E_i.\mathrm{lev}$ and is killed by $N$ in the group law, and $P$ factors through the extra level subscheme $u_i.2.\mathrm{levK}$ iff its image factors through $E_i.\mathrm{lev}$ and is killed by $\ell$. Here factoring through a morphism means the $T$-point is the composite of some morphism to the source with it, and being killed by $n$ means the $n$-fold iterate of the group law on the point equals the identity section. The conclusion is `FakeEllipticCurve.WithExtraLevel.Iso u₁ u₂`: there is an isomorphism $u_1.1.A \cong u_2.1.A$ over $\operatorname{Spec} S$ which is a homomorphism on $T$-points, commutes with the $\Lambda$-action, and matches both the level-$N$ subschemes and the extra level subschemes on $T$-points.
--
--   The statement says that the passage from a level-$N\ell$ structure to a pair (level $N$, extra level at $\ell$), characterised here by the two torsion-and-level conditions on points, respects isomorphism: isomorphic level-$N\ell$ curves have isomorphic splittings. It is used in the construction of coarse moduli for the pair problem, in [`CerednikDrinfeld.QM.IsCoarseModuliT.exists_isCoarseModuli_mul_of_coprime_of_isUnit`](thm.html#CerednikDrinfeld.QM.IsCoarseModuliT.exists_isCoarseModuli_mul_of_coprime_of_isUnit). No coprimality of $N$ and $\ell$, and no invertibility, is assumed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_iso_of_forall_factorsThrough_iff_mul.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_iso_of_forall_factorsThrough_iff_mul
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {S : Type} [CommRing S]
    (E₁ E₂ : FakeEllipticCurve Λ (N * ℓ) S) (h : FakeEllipticCurve.Iso E₁ E₂)
    (u₁ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
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
    (u₂ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
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
    FakeEllipticCurve.WithExtraLevel.Iso u₁ u₂ := by sorry
