-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_app_ratio_eq_of_sections_eq
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.app_ratio_eq_of_sections_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:11.709733+00:00
-- url     : https://prove2.me/theorems/2b6217d6-3ce9-4495-a9cf-b241b41374c5
-- title:
--   Matching sections under an isomorphism gives matching projective ratio functions
-- statement:
--   Let $P_1$ and $P_2$ present isomorphic modules, let $inc$ match the sections under the isomorphism, and assume each chart of $P_1$ lies in the corresponding chart of $P_2$. Then for all indices $i,j$, the ratio section of $P_1$ equals the restriction of the matched ratio section of $P_2$: $$r^{P_1}_{i,j}=r^{P_2}_{inc(i),inc(j)}|_{U^{P_1}_i}.$$ This compares coordinate functions between nested presentations.
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

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.app_ratio_eq_of_sections_eq {K : Type} [Field K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {M₁ M₂ : X.Modules} {N₁ N₂ : ℕ}
    (P₁ : M₁.ProjPresentation f N₁) (P₂ : M₂.ProjPresentation f N₂)
    (e : M₁ ≅ M₂) (inc : Fin (N₁ + 1) → Fin (N₂ + 1))
    (hσ : ∀ i, e.hom.app ⊤ (P₁.σ i) = P₂.σ (inc i))
    (hU : ∀ i, P₁.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i) ≤
      P₂.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (inc i)))
    (i j : Fin (N₁ + 1)) :
    P₁.toProj.app (Proj.basicOpen _ (MvPolynomial.X i))
        (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio K N₁ i j)) =
      X.presheaf.map (homOfLE (hU i)).op
        (P₂.toProj.app (Proj.basicOpen _ (MvPolynomial.X (inc i)))
          (Proj.awayToSection _ (MvPolynomial.X (inc i))
            (ProjSpace.ratio K N₂ (inc i) (inc j)))) := by sorry
