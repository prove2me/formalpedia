-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_baseChange_negMor_comp_fst
-- name    : AlgebraicGeometry.Polarisation.baseChange_negMor_comp_fst
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:08.621982+00:00
-- url     : https://prove2.me/theorems/5277b2ea-acda-4c8d-85c5-b58a577852e3
-- title:
--   Negation commutes with base change of a relative group law
-- statement:
--   Let $A→Spec(k)$ carry a relative group law $G$, and let $A'=A×_k k'$ under a field extension. If $p:A'→A$ is the projection, then $$p∘[-1]_{A'}=[-1]_A∘p.$$ This compatibility is used to base-change symmetric line-bundle identities.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
open AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.baseChange_negMor_comp_fst {k k' : Type} [Field k] [Field k']
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)} (G : RelativeGroupLaw k f)
    (b : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) :
    negMor (pullback.snd f b) (G.baseChange b) ≫ pullback.fst f b =
      pullback.fst f b ≫ negMor f G := by sorry
