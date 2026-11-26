-- Prove2me | Theorems.Thm_BKAR_Forest_localRecursiveBoundaryRemainder_eq_sum_integral_boundarySupportOrderTreeContribution_of_activeEdges_card_le
-- name    : BKAR.Forest.localRecursiveBoundaryRemainder_eq_sum_integral_boundarySupportOrderTreeContribution_of_activeEdges_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:01:47.717792+00:00
-- url     : https://prove2.me/theorems/fde7859d-b714-4dcf-94e6-5cf212915824
-- title:
--   Forest: local Recursive Boundary Remainder eq sum integral boundary Support Order Tree Contribution of active Edges card le
-- statement:
--   The local recursive remainder folds into the exact recursive support/order
--   tree contribution below the current node.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L243-L340
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L243-L340

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.localRecursiveBoundaryRemainder_eq_sum_integral_boundarySupportOrderTreeContribution_of_activeEdges_card_le
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      pref.toFinset = F.edges →
      pref.Nodup →
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ →
      localRecursiveBoundaryRemainder choices F pref prefixTs top ρ =
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            boundarySupportOrderTreeContribution choices
              (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
              t ρ)
  := by sorry
