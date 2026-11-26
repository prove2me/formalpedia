-- Prove2me | Theorems.Thm_BKAR_Forest_firstRecursiveBoundaryRemainder_eq_zero_of_forall_child_activeEdges_eq_empty
-- name    : BKAR.Forest.firstRecursiveBoundaryRemainder_eq_zero_of_forall_child_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:15:37.36084+00:00
-- url     : https://prove2.me/theorems/46a4276f-c2d6-5248-b06d-8f20705f8340
-- title:
--   Forest: first Recursive Boundary Remainder eq zero of forall child active Edges eq empty
-- statement:
--   If every first child is already terminal, the recursive boundary remainder is
--   zero.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L516-L529
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L516-L529

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.firstRecursiveBoundaryRemainder_eq_zero_of_forall_child_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hterm : ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
      (choices (Forest.empty V) e).forest.activeEdges = ∅) :
    firstRecursiveBoundaryRemainder choices ρ = 0 := by sorry
