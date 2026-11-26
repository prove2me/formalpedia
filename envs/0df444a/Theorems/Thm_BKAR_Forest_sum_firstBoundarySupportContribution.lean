-- Prove2me | Theorems.Thm_BKAR_Forest_sum_firstBoundarySupportContribution
-- name    : BKAR.Forest.sum_firstBoundarySupportContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:15:27.987988+00:00
-- url     : https://prove2.me/theorems/1125f1d3-e6af-582e-aa9d-3c13fcf4130e
-- title:
--   Forest: sum first Boundary Support Contribution
-- statement:
--   Exposed first boundary sectors regroup by finite support.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L386-L412
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L386-L412

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_firstBoundarySupportContribution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Forest.empty V).activeEdges.attach
        (fun e =>
          (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ) =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => firstBoundarySupportContribution choices I ρ) := by sorry
