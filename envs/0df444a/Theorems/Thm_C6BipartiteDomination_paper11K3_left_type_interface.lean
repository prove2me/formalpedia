-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K3_left_type_interface
-- name    : C6BipartiteDomination.paper11K3_left_type_interface
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:04:21.342183+00:00
-- url     : https://prove2.me/theorems/b0cff26e-a646-4952-8d99-3d2ad3096475
-- title:
--   C6 Bipartite Domination: paper11 K3 left type interface
-- statement:
--   The type-indexed form of the left interface: `(3,3)` supports have one
--   chosen edge and debt at most four, while `(3,2)` supports have two chosen
--   edges and debt at most seven.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L375-L409
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L375-L409

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K3_left_type_interface {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K3Supports G D) :
    (kCharge G D w = 3 ∧ betaCharge G D w = 3 ∧
      paper11LeftDegree (paper11K3Edges G D hCan hmax)
        (paper11K3RightVertices G D hCan hmax) w = 1 ∧
      -externalCharge G D w ≤ 4) ∨
    (kCharge G D w = 3 ∧ betaCharge G D w = 2 ∧
      paper11LeftDegree (paper11K3Edges G D hCan hmax)
        (paper11K3RightVertices G D hCan hmax) w = 2 ∧
      -externalCharge G D w ≤ 7) := by sorry
