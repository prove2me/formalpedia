-- Prove2me | Theorems.Thm_BKAR_Forest_firstBoundarySupportContribution_def
-- name    : BKAR.Forest.firstBoundarySupportContribution_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:59:09.446615+00:00
-- url     : https://prove2.me/theorems/8d77159f-84f0-5f64-8d41-2cb637d19186
-- title:
--   Forest: first Boundary Support Contribution def
-- statement:
--   The Forest construction uses the first Boundary Support Contribution def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L313-L322
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L313-L322

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.firstBoundarySupportContribution_def
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    firstBoundarySupportContribution choices I ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e => (choices (Forest.empty V) e).forest.support = I))
        (fun e =>
          (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ) := by sorry
