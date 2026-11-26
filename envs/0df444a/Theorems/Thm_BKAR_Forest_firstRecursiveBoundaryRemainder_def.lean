-- Prove2me | Theorems.Thm_BKAR_Forest_firstRecursiveBoundaryRemainder_def
-- name    : BKAR.Forest.firstRecursiveBoundaryRemainder_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:59:43.310872+00:00
-- url     : https://prove2.me/theorems/45d6e9a4-dda5-59fc-97e6-5ab140bf640e
-- title:
--   Forest: first Recursive Boundary Remainder def
-- statement:
--   The Forest construction uses the first Recursive Boundary Remainder def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L498-L510
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L498-L510

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.firstRecursiveBoundaryRemainder_def
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    firstRecursiveBoundaryRemainder choices ρ =
      Finset.sum (Forest.empty V).activeEdges.attach
        (fun e => ∫ t in 0..(1 : ℝ),
          Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                (choices ((choices (Forest.empty V) e).forest) e').forest
                ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ)) := by sorry
