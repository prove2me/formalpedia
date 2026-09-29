-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isPullback_of_withExtraLevel_isPullback_of_forall_factorsThrough_iff_mul
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isPullback_of_withExtraLevel_isPullback_of_forall_factorsThrough_iff_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/44b96084-05f5-5d1a-914d-9bcc7492ada1
-- title:
--   Transport of pullbacks from (N,ℓ)-pairs to level Nℓ
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and coprime naturals $N,\ell$. Let $\varphi : S \to S'$ be a homomorphism of commutative rings, let $u$ be a pair consisting of a fake elliptic curve of level $N$ over $S$ together with an extra level structure at $\ell$, and $u'$ such a pair over $S'$, and assume `FakeEllipticCurve.WithExtraLevel.IsPullback φ u u'`: there is $g : A_{u'} \to A_u$ whose square with $f_{u'}$, $f_u$ and $\operatorname{Spec}\varphi$ is cartesian, which is compatible with the relative group laws on $T$-points, satisfies $\mathrm{act}_{u'}(x) \text{ followed by } g = g \text{ followed by } \mathrm{act}_u(x)$ for all $x \in \Lambda$, and carries $T$-points factoring through $\mathrm{lev}_{u'}$ (resp. $\mathrm{levK}_{u'}$) to points whose composite with $g$ factors through $\mathrm{lev}_u$ (resp. $\mathrm{levK}_u$). Let further $E$ be a fake elliptic curve of level $N\ell$ over $S$ and $e : A_u \cong A_E$ an isomorphism with $e \text{ followed by } f_E = f_u$, such that pushing $T$-points along $e$ respects the group laws, $e$ intertwines the two $\Lambda$-actions, and a $T$-point $P$ factors through $\mathrm{lev}_u$ exactly when its image factors through $\mathrm{lev}_E$ and is killed by $N$, and factors through $\mathrm{levK}_u$ exactly when its image factors through $\mathrm{lev}_E$ and is killed by $\ell$; let $E'$, $e'$ satisfy the same four conditions over $S'$. Then `FakeEllipticCurve.IsPullback φ E E'` holds: some $E'.A \to E.A$ forms a cartesian square with $f_{E'}$, $f_E$, $\operatorname{Spec}\varphi$, is multiplicative on $T$-points, is $\Lambda$-equivariant, and carries points factoring through $\mathrm{lev}_{E'}$ to points factoring through $\mathrm{lev}_E$.
--
--   This records that the identification of pairs (level $N$ structure together with an extra level structure at $\ell$) with level $N\ell$ structures is compatible with base change along a ring homomorphism, the cartesian square and the level clause being transported through the given isomorphisms of abelian schemes. It is used in the construction of coarse moduli at level $N\ell$ from coarse moduli for the pairs, in [`CerednikDrinfeld.QM.IsCoarseModuliT.exists_isCoarseModuli_mul_of_coprime_of_isUnit`](thm.html#CerednikDrinfeld.QM.IsCoarseModuliT.exists_isCoarseModuli_mul_of_coprime_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isPullback_of_withExtraLevel_isPullback_of_forall_factorsThrough_iff_mul.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isPullback_of_withExtraLevel_isPullback_of_forall_factorsThrough_iff_mul
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} (hNℓ : N.Coprime ℓ) {S S' : Type} [CommRing S] [CommRing S']
    (φ : S →+* S')
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S')
    (h : FakeEllipticCurve.WithExtraLevel.IsPullback φ u u')
    (E : FakeEllipticCurve Λ (N * ℓ) S)
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
    (E' : FakeEllipticCurve Λ (N * ℓ) S')
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
    FakeEllipticCurve.IsPullback φ E E' := by sorry
