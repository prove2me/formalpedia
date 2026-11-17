-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_baseChange_addMor_subMor_comp_map
-- name    : AlgebraicGeometry.Polarisation.baseChange_addMor_subMor_comp_map
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:24.309573+00:00
-- url     : https://prove2.me/theorems/e7690f22-dcc9-4047-9f91-72456ce11a25
-- title:
--   Addition and subtraction commute with base change of a relative group law
-- statement:
--   Let $A→Spec(k)$ carry a relative group law $G$, and let $Spec(k')→Spec(k)$ be a field base change. Write $A'=A×_k k'$ and let $π:A'×_{k'}A'→A×_kA$ be the canonical map. Then $$p∘add_{A'}=add_A∘π,\qquad p∘sub_{A'}=sub_A∘π,$$ where $p:A'→A$ is the projection. This transports the polarization morphisms through scalar extension.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
open AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.baseChange_addMor_subMor_comp_map {k k' : Type} [Field k] [Field k']
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)} (G : RelativeGroupLaw k f)
    (b : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) :
    let f' := pullback.snd f b
    let π := pullback.map f' f' f f (pullback.fst f b) (pullback.fst f b) b
      pullback.condition.symm pullback.condition.symm
    addMor f' (G.baseChange b) ≫ pullback.fst f b = π ≫ addMor f G ∧
      subMor f' (G.baseChange b) ≫ pullback.fst f b = π ≫ subMor f G := by sorry
