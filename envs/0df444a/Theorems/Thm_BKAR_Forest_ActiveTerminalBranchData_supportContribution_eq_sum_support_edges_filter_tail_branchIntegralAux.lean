-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_eq_sum_support_edges_filter_tail_branchIntegralAux
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportContribution_eq_sum_support_edges_filter_tail_branchIntegralAux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:55:43.322231+00:00
-- url     : https://prove2.me/theorems/3ff1815e-de72-5eb0-a447-2cb516168a7d
-- title:
--   Active Terminal Branch Data: support Contribution eq sum support edges filter tail branch Integral Aux
-- statement:
--   Recursive support-fiber form: over a fixed support `I`, each admissible first
--   edge contributes the tail branch integral after that first edge.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L265-L286
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L265-L286

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.supportContribution_eq_sum_support_edges_filter_tail_branchIntegralAux
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ =
      Finset.sum
        (I.edges.attach.filter
          (fun e =>
            (data.tail (emptyActiveEdge e.val)).order ∈
              edgeSetOrders (I.edges.erase e.val)))
        (fun e => ∫ t in 0..(1 : ℝ),
          (data.tail (emptyActiveEdge e.val)).branchIntegralAux t
            ((data.extension (emptyActiveEdge e.val)).extension.extendParam
              emptyParam t)
            (partialDeriv e.val ρ)) := by sorry
