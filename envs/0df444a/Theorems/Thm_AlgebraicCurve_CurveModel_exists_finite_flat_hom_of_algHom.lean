-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_exists_finite_flat_hom_of_algHom
-- name    : AlgebraicCurve.CurveModel.exists_finite_flat_hom_of_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/5fef2a9f-b97d-5cfa-8b1b-a3dbd3b56c8c
-- title:
--   Finite function-field embeddings realised by finite flat morphisms of models
-- statement:
--   Let $K$ be a field and let $F$, $F'$ be fields equipped with $K$-algebra structures (all in possibly different universes). Let $M$ and $M'$ be curve models of $F$ and of $F'$ over $K$: each consists of an integral scheme $C$ with a proper, smooth of relative dimension one structure morphism to $\operatorname{Spec} K$, a ring isomorphism `ffEquiv` of the given field with the function field of $C$ that is compatible with $K$, and a bijection `placeOfPoint` from the closed points of $C$ onto the places of the field over $K$ (valuation subrings containing the image of $K$, proper, and principal ideal rings), such that the image of the local ring at a closed point inside the function field is the corresponding valuation subring, and every finite set of points lies in an affine open. Let $\varphi : F \to F'$ be a $K$-algebra map whose underlying ring map is integral and along which $F'$ is a finite $F$-module. Then there is a morphism $\pi : M'.C \to M.C$ such that: $\pi$ followed by the structure morphism of $M$ is that of $M'$; $\pi$ is finite, flat and locally of finite presentation; at every point of $M.C$ its rank equals the $F$-module rank of $F'$ along $\varphi$; the canonical morphism from the spectrum of the stalk at the generic point of $M'.C$ followed by $\pi$ agrees with $\operatorname{Spec}$ of the map $M.C$'s function field $\to F \to F' \to$ $M'.C$'s function field induced by $\varphi$ and the two identifications, followed by the corresponding canonical morphism for $M$; every closed point $y$ of $M'.C$ has closed image, and the place attached to $\pi(y)$ is the preimage under $\varphi$ of the place attached to $y$; and $\pi$ is the unique morphism $M'.C \to M.C$ with the stated restriction to the generic point.
--
--   This is the classical statement that a finite embedding of one-variable function fields over $K$ is induced by a unique finite flat morphism of smooth proper models, of degree the field degree and compatible with places; unlike the variant assuming characteristic zero, it is stated here for arbitrary $K$. It is used in the computation of places under Frobenius-type morphisms, in the construction of pushforward maps on degree-zero Picard groups, and in the Cherednik–Drinfeld moduli tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_exists_finite_flat_hom_of_algHom.lean

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace AlgebraicCurve.CurveModel

theorem exists_finite_flat_hom_of_algHom {K : Type u} [Field K]
    {F : Type v} {F' : Type w} [Field F] [Algebra K F] [Field F'] [Algebra K F']
    (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) :
    ∃ π : M'.C ⟶ M.C,
      π ≫ M.toBase = M'.toBase ∧
      IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧
      (∀ x : M.C, π.finrank x = finrankAlong K φ) ∧
      M'.C.fromSpecStalk (genericPoint M'.C) ≫ π =
        Spec.map (CommRingCat.ofHom
          (M'.ffEquiv.toRingHom.comp (φ.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C) ∧
      (∀ y : closedPoints M'.C, ∃ h : π.base y.1 ∈ closedPoints M.C,
        M.placeOfPoint ⟨π.base y.1, h⟩ = (M'.placeOfPoint y).restrictAlong φ hφ) ∧
      ∀ π' : M'.C ⟶ M.C,
        M'.C.fromSpecStalk (genericPoint M'.C) ≫ π' =
          M'.C.fromSpecStalk (genericPoint M'.C) ≫ π → π' = π := by sorry
