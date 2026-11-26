-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_contDiff_of_allBranchesAnalytic
-- name    : BKAR.BKARContDiff.rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_contDiff_of_allBranchesAnalytic
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:20:01.716805+00:00
-- url     : https://prove2.me/theorems/53f0fca8-89c9-4a0b-83ff-7c4037d2aa8f
-- title:
--   BKARCont Diff: rho one Config eq zero Config add sum boundary Support Order Tree Fiber filter edges ne empty of cont Diff of all Branches Analytic
-- statement:
--   Final flattened root identity with the fiber-integrability obligation
--   discharged by `BKARContDiff`. The remaining analytic input is the
--   all-branches induction hypothesis.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberSmoothness.lean#L344-L361
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberSmoothness.lean#L344-L361

import Definitions.Def_BKAR_CubePartition_Smoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_contDiff_of_allBranchesAnalytic
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (hanalytic :
      Forest.allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      ρ zeroConfig +
        Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => I.edges ≠ ∅))
          (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
            (fun order =>
              Forest.boundarySupportOrderTreeFiber choices (Forest.empty V)
                [] [] 1 I order ρ)) := by sorry
