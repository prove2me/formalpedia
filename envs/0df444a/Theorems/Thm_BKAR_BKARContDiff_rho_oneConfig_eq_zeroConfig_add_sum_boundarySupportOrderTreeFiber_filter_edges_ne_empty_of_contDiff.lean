-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_contDiff
-- name    : BKAR.BKARContDiff.rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_contDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:12:21.433464+00:00
-- url     : https://prove2.me/theorems/f300f290-9599-52c0-a961-2e7c7069a403
-- title:
--   BKARCont Diff: rho one Config eq zero Config add sum boundary Support Order Tree Fiber filter edges ne empty of cont Diff
-- statement:
--   Final flattened root identity with both the analytic recursion predicate and
--   the nontrivial fiber-integrability predicate discharged by `BKARContDiff`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L392-L404
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L392-L404

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_contDiff
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ρ oneConfig =
      ρ zeroConfig +
        Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => I.edges ≠ ∅))
          (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
            (fun order =>
              Forest.boundarySupportOrderTreeFiber choices (Forest.empty V)
                [] [] 1 I order ρ)) := by sorry
