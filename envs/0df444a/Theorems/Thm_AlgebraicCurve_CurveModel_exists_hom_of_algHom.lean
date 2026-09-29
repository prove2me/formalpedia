-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_exists_hom_of_algHom
-- name    : AlgebraicCurve.CurveModel.exists_hom_of_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/0b845d46-2e2d-5dfe-a6f4-3fb1f63387c4
-- title:
--   Finite flat morphism of curve models induced by a function-field embedding
-- statement:
--   Let $K$ be a field of characteristic zero, and let $F$, $F'$ be fields that are $K$-algebras. Let $M$ and $M'$ be curve models over $K$ of $F$ and of $F'$ respectively; that is, each consists of an integral scheme $C$ together with a proper, smooth of relative dimension $1$ morphism $C \to \operatorname{Spec} K$, a ring isomorphism of the given field with the function field of $C$ compatible with the structure map from $K$, a bijection from the closed points of $C$ onto the places of the field over $K$ (valuation subrings, not the whole field, containing the image of $K$ and with principal ideals) matching each stalk with the corresponding valuation subring, and the property that every finite set of points of $C$ lies in an affine open. Let $\varphi : F \to_{\mathrm{alg}[K]} F'$ be a $K$-algebra map such that $F'$ is integral over $F$ via $\varphi$ and, viewing $F'$ as an $F$-module via $\varphi$, is a finite module. Then there exists a morphism $\pi : M'.C \to M.C$ such that: $\pi$ followed by the structure map of $M$ is the structure map of $M'$; $\pi$ is finite, flat and locally of finite presentation; at every point $x$ of $M.C$ the flat rank of $\pi$ equals $\operatorname{finrank}_F F'$; on generic stalks, $M'.C.\mathrm{fromSpecStalk}$ at the generic point followed by $\pi$ coincides with $\operatorname{Spec}$ of the ring map $M.C$-function field $\to M'.C$-function field obtained by transporting $\varphi$ through the two function-field isomorphisms, followed by $M.C.\mathrm{fromSpecStalk}$ at the generic point; for every closed point $y$ of $M'.C$, the image $\pi(y)$ is a closed point of $M.C$ whose associated place is the restriction along $\varphi$ (the preimage valuation subring) of the place associated with $y$; and $\pi$ is the unique morphism $M'.C \to M.C$ with the stated composite with $M'.C.\mathrm{fromSpecStalk}$ at the generic point.
--
--   This is the geometric half of the anti-equivalence between smooth proper curves over $K$ and one-variable function fields over $K$: a finite embedding of function fields is realised by a unique finite flat morphism of models, compatibly with places and hence with divisors. It is used to produce morphisms between modular curve models, in particular the correspondences underlying Hecke endomorphisms of relative Jacobians, and to compare two models of the same field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_exists_hom_of_algHom.lean

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve.CurveModel

theorem exists_hom_of_algHom {K : Type u} [Field K] [CharZero K]
    {F F' : Type u} [Field F] [Algebra K F] [Field F'] [Algebra K F']
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
