-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_isOpenImmersion_of_functionField_iso
-- name    : AlgebraicGeometry.Scheme.exists_isOpenImmersion_of_functionField_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/935b19f9-41e5-5088-a31d-8f540b1674bc
-- title:
--   Birational integral K-schemes: open immersion near the generic point
-- statement:
--   Let $K$ be a field, and let $C$, $C'$ be schemes over $K$ by means of structure morphisms $c \colon C \to \operatorname{Spec} K$ and $c' \colon C' \to \operatorname{Spec} K$, both $C$ and $C'$ being integral and both $c$ and $c'$ locally of finite type. Write $\operatorname{Spec} \mathcal{O}_{C,\eta} \to C$ for the canonical morphism from the spectrum of the stalk at the generic point $\eta$ of $C$, and likewise for $C'$; the stalk at the generic point of an integral scheme is the function field. Assume given an isomorphism $\psi \colon K(C) \xrightarrow{\sim} K(C')$ of commutative rings between the function fields, compatible with the structure morphisms in the sense that $\operatorname{Spec}(\psi^{-1})$ followed by the canonical morphism $\operatorname{Spec} K(C') \to C'$ and then by $c'$ agrees with the canonical morphism $\operatorname{Spec} K(C) \to C$ followed by $c$. Then there are an open subscheme $U \subseteq C$ containing the generic point of $C$ and a morphism $j \colon U \to C'$ which is an open immersion, such that $j$ followed by $c'$ equals the inclusion $U \hookrightarrow C$ followed by $c$ (so $j$ is a morphism over $K$), and such that the canonical morphism $\operatorname{Spec} \mathcal{O}_{U,\eta} \to U$ followed by $j$ equals $\operatorname{Spec}(\psi^{-1})$ followed by the canonical morphism $\operatorname{Spec} K(C') \to C'$ (so $j$ induces $\psi$ on function fields).
--
--   This is the scheme-theoretic form of the classical statement that birational integral varieties over a field have isomorphic non-empty open subschemes, with no properness, separatedness, smoothness or dimension hypothesis, and with the induced map on function fields prescribed. It is used in the construction of models of algebraic curves, where it supplies the open immersion comparing two models with the same function field over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_isOpenImmersion_of_functionField_iso.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_isOpenImmersion_of_functionField_iso
    {K : Type u} [Field K] {C C' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (c' : C' ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsIntegral C'] [LocallyOfFiniteType c] [LocallyOfFiniteType c']
    (ψ : C.functionField ≅ C'.functionField)
    (hψ : Spec.map ψ.inv ≫ C'.fromSpecStalk (genericPoint C') ≫ c' =
      C.fromSpecStalk (genericPoint C) ≫ c) :
    ∃ (U : C.Opens) (hη : genericPoint C ∈ U) (j : (U : Scheme.{u}) ⟶ C') (_ : IsOpenImmersion j),
      j ≫ c' = U.ι ≫ c ∧
      U.fromSpecStalkOfMem (genericPoint C) hη ≫ j =
        Spec.map ψ.inv ≫ C'.fromSpecStalk (genericPoint C') := by sorry
