-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_levelOne_extraLevel_and_exists_of_extraLevel
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_levelOne_extraLevel_and_exists_of_extraLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/9e5e94a2-852f-5b98-98aa-41a9e571d2d2
-- title:
--   Level-N data and extra levels at N correspond
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$ and a commutative ring $S$. Recall that an object of `FakeEllipticCurve Λ N S` consists of a scheme $A$ over $\operatorname{Spec} S$ which is smooth, proper, with connected and two‑dimensional fibres, a commutative relative group law $L$ on the functor of points over $\operatorname{Spec} S$, an action `act` of $\Lambda$ by endomorphisms of $A$ over $S$ that is additive and multiplicative, respects $L$ and satisfies the trace condition, together with a level morphism `lev` out of a scheme $C$; and that an element of `E₁.ExtraLevel N` is a closed immersion `levK` into $E_1.A$ whose points are a subgroup for $L$, killed by $N$, $\Lambda$‑stable, meeting the points of $E_1$'s `lev` only in the unit, with `levK` followed by the structure morphism finite, flat, locally of finite presentation, of fibre rank $N^2$, and geometric fibres $(\mathbb{Z}/N)^2$ over algebraically closed fields in which $N$ is invertible. The assertion is a two‑way statement. First, every $E$ of level $N$ admits an $E_1$ of level $1$, an extra level $K$ at $N$ on $E_1$, and an isomorphism $e \colon E.A \cong E_1.A$ with $E_1.f \circ e = E.f$ such that, for every test morphism $t \colon T \to \operatorname{Spec} S$, composition with $e$ carries the group law of $E$ to that of $E_1$, $e$ intertwines the two $\Lambda$‑actions, and a point of $E$ over $t$ factors through `E.lev` exactly when its image factors through `K.levK`. Secondly, conversely, every level‑one $E_1$ with an extra level $K$ at $N$ arises in this way from some $E$ of level $N$, with an isomorphism $e$ having the same three properties.
--
--   This is the dictionary between the two slots of the moduli vocabulary for fake elliptic curves: a level‑$N$ datum on an abelian surface with quaternionic multiplication is the same thing as an extra level at $N$ on the corresponding level‑one object. It is used where level structures have to be read in either format, in particular in the existence and isomorphism statements for fake elliptic curves with prescribed quaternionic data and in the construction of finite étale fine moduli from local data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_levelOne_extraLevel_and_exists_of_extraLevel.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_levelOne_extraLevel_and_exists_of_extraLevel
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) (S : Type u) [CommRing S] :
    (∀ E : FakeEllipticCurve Λ N S,
      ∃ (E₁ : FakeEllipticCurve Λ 1 S) (K : E₁.ExtraLevel N) (e : E.A ≅ E₁.A) (he : e.hom ≫ E₁.f = E.f),
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
          mapPt e.hom he (E.L.mul t P Q) = E₁.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
        (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E₁.act x) ∧
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
          FactorsThrough E.lev P ↔ FactorsThrough K.levK (mapPt e.hom he P))) ∧
    (∀ (E₁ : FakeEllipticCurve Λ 1 S) (K : E₁.ExtraLevel N),
      ∃ (E : FakeEllipticCurve Λ N S) (e : E.A ≅ E₁.A) (he : e.hom ≫ E₁.f = E.f),
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
          mapPt e.hom he (E.L.mul t P Q) = E₁.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
        (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E₁.act x) ∧
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
          FactorsThrough E.lev P ↔ FactorsThrough K.levK (mapPt e.hom he P))) := by sorry
