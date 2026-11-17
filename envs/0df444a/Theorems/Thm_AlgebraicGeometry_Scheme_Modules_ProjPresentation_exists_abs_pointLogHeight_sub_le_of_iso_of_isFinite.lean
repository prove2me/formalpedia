-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_abs_pointLogHeight_sub_le_of_iso_of_isFinite
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_abs_pointLogHeight_sub_le_of_iso_of_isFinite
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:53.148061+00:00
-- url     : https://prove2.me/theorems/90133006-7355-45a1-8ab9-56b77e68e0ea
-- title:
--   Heights from finite projective presentations of isomorphic modules differ by a bounded amount
-- statement:
--   Let $K$ be a number field, let $P_1$ and $P_2$ be projective presentations of isomorphic modules on a $K$-scheme, and assume the morphism defined by $P_1$ is finite. Then there is $C≥0$ such that for every $K$-point $x$, $$|h_{P_1}(x)-h_{P_2}(x)|≤C.$$ This supplies the bounded-change principle needed when replacing one height presentation by another.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_abs_pointLogHeight_sub_le_of_iso_of_isFinite {K : Type} [Field K] [NumberField K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)} {M₁ M₂ : X.Modules} {N₁ N₂ : ℕ}
    (P₁ : M₁.ProjPresentation f N₁) (P₂ : M₂.ProjPresentation f N₂) (e : M₁ ≅ M₂)
    (hfin : IsFinite P₁.toProj) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Scheme.KPoint f, |P₁.pointLogHeight x - P₂.pointLogHeight x| ≤ C := by sorry
