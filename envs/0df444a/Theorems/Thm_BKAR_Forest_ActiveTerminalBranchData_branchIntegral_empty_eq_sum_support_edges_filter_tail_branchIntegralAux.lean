-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegral_empty_eq_sum_support_edges_filter_tail_branchIntegralAux
-- name    : BKAR.Forest.ActiveTerminalBranchData.branchIntegral_empty_eq_sum_support_edges_filter_tail_branchIntegralAux
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:29:11.527576+00:00
-- url     : https://prove2.me/theorems/c89e2e28-2a5a-5831-a22d-ab2c1da6faa7
-- title:
--   Active Terminal Branch Data: branch Integral empty eq sum support edges filter tail branch Integral Aux
-- statement:
--   Full empty-start recursive form after regrouping by terminal support: the
--   selected terminal branch sum is a support-indexed sum of tail branch integrals.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L292-L312
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L292-L312

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

theorem BKAR.Forest.ActiveTerminalBranchData.branchIntegral_empty_eq_sum_support_edges_filter_tail_branchIntegralAux
    (data : ActiveTerminalBranchData (Forest.empty V))
    (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I =>
          Finset.sum
            (I.edges.attach.filter
              (fun e =>
                (data.tail (emptyActiveEdge e.val)).order ∈
                  edgeSetOrders (I.edges.erase e.val)))
            (fun e => ∫ t in 0..(1 : ℝ),
              (data.tail (emptyActiveEdge e.val)).branchIntegralAux t
                ((data.extension (emptyActiveEdge e.val)).extension.extendParam
                  emptyParam t)
                (partialDeriv e.val ρ))) := by sorry
