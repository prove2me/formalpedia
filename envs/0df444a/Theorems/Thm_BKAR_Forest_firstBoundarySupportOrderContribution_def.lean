-- Prove2me | Theorems.Thm_BKAR_Forest_firstBoundarySupportOrderContribution_def
-- name    : BKAR.Forest.firstBoundarySupportOrderContribution_def
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:59:35.847596+00:00
-- url     : https://prove2.me/theorems/51cad76d-4548-46f5-ab65-896e1150f689
-- title:
--   Forest: first Boundary Support Order Contribution def
-- statement:
--   The Forest construction uses the first Boundary Support Order Contribution def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L342-L354
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L342-L354

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.firstBoundarySupportOrderContribution_def
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    firstBoundarySupportOrderContribution choices I order ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e =>
            (choices (Forest.empty V) e).forest.support = I ∧
              [e.val] = order))
        (fun e =>
          (choices (Forest.empty V) e).forest.orderedContribution order ρ) := by sorry
