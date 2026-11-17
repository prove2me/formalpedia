-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_appLE_awayToSection_eq_of_specMap
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.appLE_awayToSection_eq_of_specMap
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:13:30.739068+00:00
-- url     : https://prove2.me/theorems/acd4d21e-bb9a-47f0-bb77-512da21f2c6a
-- title:
--   Pulling back a localized projective section evaluates it by the chart homomorphism
-- statement:
--   Let $y:Spec(K)→ℙ^N_K$ factor through the chart $D_+(X_i)$ by a ring map $φ$, and assume the whole source lies over that chart. For every element $z$ of the homogeneous localization at $X_i$, the induced pullback on sections, followed by the canonical identification $Γ(Spec K)≅K$, satisfies $$y^*(z)=φ(z).$$ This is the evaluation formula for projective chart sections. Formalization note: the open-containment hypothesis records the domain on which the sheaf map is evaluated.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.appLE_awayToSection_eq_of_specMap
    {K : Type} [Field K] {N : ℕ}
    (y : Spec (CommRingCat.of K) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (i : Fin (N + 1))
    (φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
      (MvPolynomial.X i) →+* K)
    (hy : y = Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i)
      (ProjSpace.X_mem_one K N i) one_pos)
    (hle : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤
      y ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i))
    (z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
      (MvPolynomial.X i)) :
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom
      (y.appLE (Proj.basicOpen _ (MvPolynomial.X i)) ⊤ hle (Proj.awayToSection _ (MvPolynomial.X i) z)) =
      φ z := by sorry
