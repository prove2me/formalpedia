-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_exists_hom_pointEquivPlace_restrict_eq
-- name    : AlgebraicCurve.CurveModel.exists_hom_pointEquivPlace_restrict_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/26010d8c-eba5-5d7a-b3b5-4b8284edd2ca
-- title:
--   Finite extensions of function fields induce finite flat morphisms of models
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero, and let $F \subseteq F'$ be fields over $K$ with $F'$ a finite $F$-module, the $K$-algebra structures being compatible. Let $M$ be a `CurveModel K F` and $M'$ a `CurveModel K F'`: that is, each consists of an integral scheme $C$ with a proper, smooth of relative dimension $1$ morphism `toBase` to $\operatorname{Spec} K$, a ring isomorphism `ffEquiv` of the given field with the function field of $C$ that is $K$-linear in the sense of agreeing with the map induced by `toBase` on the germ at the generic point, a bijection `placeOfPoint` from the closed points of $C$ onto the places of the field over $K$ (valuation subrings containing $K$, proper, with principal ideal ring) identifying the image of each stalk in the function field with the valuation subring of the corresponding place, and the property that every finite set of points lies in an affine open. Then there is a morphism $\pi : M'.C \to M.C$ such that: $\pi$ followed by $M$.`toBase` is $M'$.`toBase`; $\pi$ is finite, flat and locally of finite presentation; the flat rank of $\pi$ at every point of $M.C$ equals $\operatorname{finrank}_F F'$; the morphism from the spectrum of the stalk at the generic point of $M'.C$ followed by $\pi$ coincides with $\operatorname{Spec}$ of the ring map $F \to F'$ transported through `ffEquiv` on both sides, followed by the corresponding morphism for $M$; for all $K$-points $y$ of $M'.C$ and $x$ of $M.C$ (sections of the structure morphisms) with $y$ followed by $\pi$ equal to $x$, the place of $F'/K$ attached to $y$ by `pointEquivPlace` restricts along $F \to F'$ (preimage of the valuation subring) to the place of $F/K$ attached to $x$; and $\pi$ is the unique morphism $M'.C \to M.C$ with the stated behaviour on the generic point.
--
--   This is the functoriality of smooth proper models of one-variable function fields with respect to a finite field extension, in the form used to compare models of modular curves: the degeneracy, Atkin–Lehner and Hecke-type morphisms between the models occurring in the modularity argument are produced by this statement and their effect on $K$-rational points is read off from the restriction of places. It is cited by the results on the model package for modular curves that identify `pointEquivPlace` of a rational point after composition with such a morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_exists_hom_pointEquivPlace_restrict_eq.lean

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve.CurveModel

theorem exists_hom_pointEquivPlace_restrict_eq {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] {F F' : Type u} [Field F] [Algebra K F] [Field F'] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [Module.Finite F F']
    (M : CurveModel K F) (M' : CurveModel K F') :
    ∃ π : M'.C ⟶ M.C,
      π ≫ M.toBase = M'.toBase ∧
      IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧
      (∀ x : M.C, π.finrank x = Module.finrank F F') ∧
      M'.C.fromSpecStalk (genericPoint M'.C) ≫ π =
        Spec.map (CommRingCat.ofHom
          (M'.ffEquiv.toRingHom.comp ((algebraMap F F').comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C) ∧
      (∀ (y : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
          (x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
        y.1 ≫ π = x.1 → (M'.pointEquivPlace y).restrict F = M.pointEquivPlace x) ∧
      ∀ π' : M'.C ⟶ M.C,
        M'.C.fromSpecStalk (genericPoint M'.C) ≫ π' =
          M'.C.fromSpecStalk (genericPoint M'.C) ≫ π → π' = π := by sorry
