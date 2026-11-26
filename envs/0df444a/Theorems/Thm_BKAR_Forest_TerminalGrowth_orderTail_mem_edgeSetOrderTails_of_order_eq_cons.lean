-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_orderTail_mem_edgeSetOrderTails_of_order_eq_cons
-- name    : BKAR.Forest.TerminalGrowth.orderTail_mem_edgeSetOrderTails_of_order_eq_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:27:32.808724+00:00
-- url     : https://prove2.me/theorems/f3408427-49d7-5133-b610-89804dcaafc9
-- title:
--   Terminal Growth: order Tail mem edge Set Order Tails of order eq cons
-- statement:
--   A nonempty empty-start terminal branch gives a member of the terminal
--   first-edge/tail-order indexing set.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L100-L115
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L100-L115

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.orderTail_mem_edgeSetOrderTails_of_order_eq_cons
    (data : TerminalGrowth (Forest.empty V))
    {e : Edge V} {order : List (Edge V)}
    (horder : data.order = e :: order) :
    ∃ he : e ∈ data.terminal.edges,
      (⟨⟨e, he⟩, order⟩ :
        Σ _ : {x : Edge V // x ∈ data.terminal.edges},
          List (Edge V)) ∈
          edgeSetOrderTails data.terminal.edges := by sorry
