-- Prove2me | Theorems.Thm_BKAR_Forest_intervalIntegrable_allBranchesBoundaryExpansion_activeEdges_card_child
-- name    : BKAR.Forest.intervalIntegrable_allBranchesBoundaryExpansion_activeEdges_card_child
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:44:29.960735+00:00
-- url     : https://prove2.me/theorems/19596783-022c-488b-8799-00d242f50b7e
-- title:
--   Forest: interval Integrable all Branches Boundary Expansion active Edges card child
-- statement:
--   The exact-depth boundary subtree below an active child is interval-integrable
--   whenever the parent exact-depth all-branches analytic hypotheses hold.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L675-L706
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L675-L706

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.intervalIntegrable_allBranchesBoundaryExpansion_activeEdges_card_child
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    IntervalIntegrable
      (fun t : ℝ =>
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ)
      MeasureTheory.volume 0 top := by sorry
