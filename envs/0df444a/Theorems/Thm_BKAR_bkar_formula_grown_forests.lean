-- Prove2me | Theorems.Thm_BKAR_bkar_formula_grown_forests
-- name    : BKAR.bkar_formula_grown_forests
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:08:27.156241+00:00
-- url     : https://prove2.me/theorems/b67747a1-c55f-531f-9a76-6cb289cb01cf
-- title:
--   BKAR: bkar formula grown forests
-- statement:
--   Public canonical-representative sector form. This removes the existential
--   `Forest`-representative bridge from each sector by choosing the forest grown by the canonical
--   order follower.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L277-L287
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L277-L287

import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Definitions.Def_BKAR_Formula
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.bkar_formula_grown_forests
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ∀ choices : Forest.ActiveExtensionChoice V,
      ρ oneConfig =
        Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (Forest.edgeSetOrders I.edges).attach
            (fun order =>
              (Forest.grownForestForSupportOrder choices I order).orderedContribution
                order.val ρ)) := by sorry
