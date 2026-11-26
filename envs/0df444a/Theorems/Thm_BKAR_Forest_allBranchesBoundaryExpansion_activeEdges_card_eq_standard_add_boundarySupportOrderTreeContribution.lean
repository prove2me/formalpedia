-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_boundarySupportOrderTreeContribution
-- name    : BKAR.Forest.allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_boundarySupportOrderTreeContribution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:47:44.004921+00:00
-- url     : https://prove2.me/theorems/139489ab-0af0-5341-a2d1-de20b25446d7
-- title:
--   Forest: all Branches Boundary Expansion active Edges card eq standard add boundary Support Order Tree Contribution
-- statement:
--   Exact-depth local boundary expansion with all recursive remainders folded into
--   the support/order tree contribution.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L381-L403
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L381-L403

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_boundarySupportOrderTreeContribution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpref : pref.toFinset = F.edges) (hnodup : pref.Nodup)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        boundarySupportOrderTreeContribution choices F pref prefixTs top ρ := by sorry
