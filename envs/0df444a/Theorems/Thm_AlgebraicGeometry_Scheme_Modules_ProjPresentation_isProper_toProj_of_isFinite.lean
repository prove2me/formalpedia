-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isProper_toProj_of_isFinite
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.isProper_toProj_of_isFinite
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:13:58.90438+00:00
-- url     : https://prove2.me/theorems/e3e0645b-d2c3-4d10-ab83-663bacd37c3e
-- title:
--   If one projective presentation is finite, every other projective presentation is proper
-- statement:
--   Let $P_1$ and $P_2$ be projective presentations on the same scheme over a field. If the morphism to projective space defined by $P_1$ is finite, then $$P_2:X→ℙ^{N_2}\text{ is proper}.$$ This makes the image of any alternative presentation closed.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.isProper_toProj_of_isFinite {K : Type} [Field K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {M₁ M₂ : X.Modules} {N₁ N₂ : ℕ}
    (P₁ : M₁.ProjPresentation f N₁) (P₂ : M₂.ProjPresentation f N₂)
    (hfin : IsFinite P₁.toProj) : IsProper P₂.toProj := by sorry
