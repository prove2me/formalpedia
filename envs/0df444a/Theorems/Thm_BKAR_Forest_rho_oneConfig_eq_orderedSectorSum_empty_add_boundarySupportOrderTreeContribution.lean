-- Prove2me | Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_boundarySupportOrderTreeContribution
-- name    : BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_boundarySupportOrderTreeContribution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:17:17.027076+00:00
-- url     : https://prove2.me/theorems/678abd07-f0f9-4f02-8436-640e2a68bbee
-- title:
--   Forest: rho one Config eq ordered Sector Sum empty add boundary Support Order Tree Contribution
-- statement:
--   Root exact boundary-tree regrouping with the recursive remainder completely
--   folded into the support/order tree contribution.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L432-L452
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L432-L452

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_boundarySupportOrderTreeContribution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        boundarySupportOrderTreeContribution choices (Forest.empty V) [] []
          1 ρ := by sorry
