-- Prove2me | Theorems.Thm_BKAR_Forest_integral_allBranchesBoundaryExpansion_empty_singleton_eq_orderedContribution
-- name    : BKAR.Forest.integral_allBranchesBoundaryExpansion_empty_singleton_eq_orderedContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:14:40.832906+00:00
-- url     : https://prove2.me/theorems/a1ce87b2-6dc6-43d1-8614-d1a58077bd18
-- title:
--   Forest: integral all Branches Boundary Expansion empty singleton eq ordered Contribution
-- statement:
--   Terminal first-edge children in the boundary tree are exactly the corresponding
--   one-edge ordered-sector contributions.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L1030-L1051
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L1030-L1051

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integral_allBranchesBoundaryExpansion_empty_singleton_eq_orderedContribution
    (choices : ActiveExtensionChoice V)
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (ρ : (Edge V → ℝ) → ℝ)
    (hterm :
      (choices (Forest.empty V) e).forest.activeEdges = ∅) :
    (∫ t in 0..(1 : ℝ),
        allBranchesBoundaryExpansion choices
          (choices (Forest.empty V) e).forest.activeEdges.card
          (choices (Forest.empty V) e).forest [e.val] [t] t ρ) =
      (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ := by sorry
