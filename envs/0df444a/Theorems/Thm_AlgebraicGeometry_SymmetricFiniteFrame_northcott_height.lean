-- Prove2me | Theorems.Thm_AlgebraicGeometry_SymmetricFiniteFrame_northcott_height
-- name    : AlgebraicGeometry.SymmetricFiniteFrame.northcott_height
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:13:45.940126+00:00
-- url     : https://prove2.me/theorems/2d7ef2d5-dc40-4e7a-8212-ca0663a168b2
-- title:
--   The height of a symmetric finite frame satisfies Northcott finiteness
-- statement:
--   Let $K$ be a number field and let $F$ be a symmetric finite frame. For every real $B$, $$\{x∈A(K):h_F(x)≤B\}\text{ is finite}.$$ This provides the finite-sublevel-set property of the height used to prove Mordell-Weil finiteness.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
open AlgebraicGeometry.SymmetricFiniteFrame

theorem AlgebraicGeometry.SymmetricFiniteFrame.northcott_height {K : Type} [Field K] [NumberField K] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of K)} {G : RelativeGroupLaw K f} (F : SymmetricFiniteFrame K f G) : ∀ B : ℝ, {x : Scheme.KPoint f | F.height x ≤ B}.Finite := by sorry
