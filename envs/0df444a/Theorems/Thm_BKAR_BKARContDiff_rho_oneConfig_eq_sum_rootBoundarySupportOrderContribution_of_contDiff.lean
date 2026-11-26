-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution_of_contDiff
-- name    : BKAR.BKARContDiff.rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution_of_contDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:12:30.137798+00:00
-- url     : https://prove2.me/theorems/0ca49779-843f-4d1a-bb14-ad9bad1bb27e
-- title:
--   BKARCont Diff: rho one Config eq sum root Boundary Support Order Contribution of cont Diff
-- statement:
--   Final-shaped root BKAR identity with the empty support/order sector packaged
--   inside `rootBoundarySupportOrderContribution`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L410-L420
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L410-L420

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution_of_contDiff
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ρ oneConfig =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
          (fun order =>
            Forest.rootBoundarySupportOrderContribution choices ρ I order)) := by sorry
