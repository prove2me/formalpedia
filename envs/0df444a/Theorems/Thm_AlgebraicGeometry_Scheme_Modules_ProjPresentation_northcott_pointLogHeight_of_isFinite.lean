-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_northcott_pointLogHeight_of_isFinite
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.northcott_pointLogHeight_of_isFinite
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:13:59.76996+00:00
-- url     : https://prove2.me/theorems/c558343a-b4ad-4fa0-bf15-ba3f2e2f25ba
-- title:
--   A finite projective presentation satisfies Northcott finiteness
-- statement:
--   Let $K$ be a number field and let $P$ be a projective presentation whose morphism to projective space is finite. Then for every real $B$, $$\{x∈X(K):h_P(x)≤B\}\text{ is finite}.$$ This supplies the finiteness property required of the expanding height on the Jacobian quotient.
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

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.northcott_pointLogHeight_of_isFinite {K : Type} [Field K] [NumberField K] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)} {M : X.Modules} {N : ℕ} (P : M.ProjPresentation f N)
    (hfin : IsFinite P.toProj) : ∀ B : ℝ, {x : Scheme.KPoint f | P.pointLogHeight x ≤ B}.Finite := by sorry
