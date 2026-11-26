-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_cons_orderedContribution_eq_integral_tail_branchIntegralAux_emptyStart
-- name    : BKAR.Forest.TerminalGrowth.cons_orderedContribution_eq_integral_tail_branchIntegralAux_emptyStart
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:49:01.853216+00:00
-- url     : https://prove2.me/theorems/268912ed-841d-4c69-91f2-73a1c820f1a3
-- title:
--   Terminal Growth: cons ordered Contribution eq integral tail branch Integral Aux empty Start
-- statement:
--   For a terminal branch obtained by first adding `e` from the empty forest, the
--   corresponding ordered-sector contribution is exactly the recursive tail
--   integral after that first edge.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L158-L173
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L158-L173

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.cons_orderedContribution_eq_integral_tail_branchIntegralAux_emptyStart
    {e : Edge V} (h : ActiveExtension (Forest.empty V) e)
    (tail : TerminalGrowth h.forest) (ρ : (Edge V → ℝ) → ℝ) :
    tail.terminal.orderedContribution (e :: tail.order) ρ =
      ∫ t in 0..(1 : ℝ),
        tail.branchIntegralAux t (h.extension.extendParam emptyParam t)
          (partialDeriv e ρ) := by sorry
