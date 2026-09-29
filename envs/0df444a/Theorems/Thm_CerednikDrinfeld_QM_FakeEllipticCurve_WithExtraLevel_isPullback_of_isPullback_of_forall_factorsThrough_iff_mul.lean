-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isPullback_of_isPullback_of_forall_factorsThrough_iff_mul
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.isPullback_of_isPullback_of_forall_factorsThrough_iff_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/42ce7822-e4eb-5c43-9f66-eadc111b958a
-- title:
--   Level splitting at (N,ℓ) commutes with base change
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N,\ell$, commutative rings $S,S'$ and a ring homomorphism $\varphi : S \to S'$. Let $E$, $E'$ be fake elliptic curves with $\Lambda$-action of level $N\ell$ over $S$ and $S'$ respectively, and suppose `FakeEllipticCurve.IsPullback φ E E'`: there is $g : E'.A \to E.A$ making the square formed with the structure morphisms and $\mathrm{Spec}\,\varphi$ cartesian, compatible with the relative group laws on $T$-points, $\Lambda$-equivariant, and carrying $T$-points factoring through $E'.\mathrm{lev}$ to points factoring through $E.\mathrm{lev}$. Let $u = (u_1,u_2)$ be a fake elliptic curve of level $N$ over $S$ together with an extra level-$\ell$ structure, and similarly $u'$ over $S'$. Assume given isomorphisms $e : u_1.A \cong E.A$ and $e' : u'_1.A \cong E'.A$ over the respective bases, which are homomorphisms for the group laws on $T$-points (via `mapPt`) and intertwine the $\Lambda$-actions, and which identify the level structures as follows: a $T$-point $P$ factors through $u_1.\mathrm{lev}$ (resp. $u_2.\mathrm{levK}$) precisely when its image factors through $E.\mathrm{lev}$ and is killed by $N$ (resp. by $\ell$) for the group law of $E$, and correspondingly for $u'$, $E'$. Then `FakeEllipticCurve.WithExtraLevel.IsPullback φ u u'` holds: there is a morphism $u'_1.A \to u_1.A$ exhibiting $u'_1$ as the base change of $u_1$ along $\varphi$, compatible with the group laws and the $\Lambda$-actions, and carrying $T$-points factoring through $u'_1.\mathrm{lev}$, resp. $u'_2.\mathrm{levK}$, to points factoring through $u_1.\mathrm{lev}$, resp. $u_2.\mathrm{levK}$.
--
--   This is the base-change compatibility of the splitting of a level-$N\ell$ structure into a level-$N$ structure together with an extra level structure at $\ell$: the cartesian datum for the level-$N\ell$ objects is transported through the given isomorphisms to the pairs. It is used in the construction of coarse moduli at composite level, in [`CerednikDrinfeld.QM.IsCoarseModuliT.exists_isCoarseModuli_mul_of_coprime_of_isUnit`](thm.html#CerednikDrinfeld.QM.IsCoarseModuliT.exists_isCoarseModuli_mul_of_coprime_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isPullback_of_isPullback_of_forall_factorsThrough_iff_mul.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.isPullback_of_isPullback_of_forall_factorsThrough_iff_mul
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : FakeEllipticCurve Λ (N * ℓ) S) (E' : FakeEllipticCurve Λ (N * ℓ) S') (h : FakeEllipticCurve.IsPullback φ E E')
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
    (e : u.1.A ≅ E.A) (he : e.hom ≫ E.f = u.1.f)
    (e_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = E.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (e_act : ∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ E.act x)
    (e_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔
        FactorsThrough E.lev (mapPt e.hom he P) ∧ nsmulPt E.L t N (mapPt e.hom he P) = E.L.one t)
    (e_levK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.2.levK P ↔
        FactorsThrough E.lev (mapPt e.hom he P) ∧ nsmulPt E.L t ℓ (mapPt e.hom he P) = E.L.one t)
    (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S')
    (e' : u'.1.A ≅ E'.A) (he' : e'.hom ≫ E'.f = u'.1.f)
    (e'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t u'.1.f),
      mapPt e'.hom he' (u'.1.L.mul t P Q) = E'.L.mul t (mapPt e'.hom he' P) (mapPt e'.hom he' Q))
    (e'_act : ∀ x : ↥Λ, u'.1.act x ≫ e'.hom = e'.hom ≫ E'.act x)
    (e'_lev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t u'.1.f),
      FactorsThrough u'.1.lev P ↔
        FactorsThrough E'.lev (mapPt e'.hom he' P) ∧ nsmulPt E'.L t N (mapPt e'.hom he' P) = E'.L.one t)
    (e'_levK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t u'.1.f),
      FactorsThrough u'.2.levK P ↔
        FactorsThrough E'.lev (mapPt e'.hom he' P) ∧ nsmulPt E'.L t ℓ (mapPt e'.hom he' P) = E'.L.one t) :
    FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' := by sorry
