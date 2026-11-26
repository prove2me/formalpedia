-- Prove2me | Theorems.Thm_BKAR_bkar_formula_grown_forest_cube_sectors
-- name    : BKAR.bkar_formula_grown_forest_cube_sectors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:15.087713+00:00
-- url     : https://prove2.me/theorems/7620f83b-29b2-4071-a28e-19ef243bc327
-- title:
--   BKAR: bkar formula grown forest cube sectors
-- statement:
--   Public canonical-representative closed-sector form. The `Forest` representative choice remaining in
--   the sector integrand is removed by the canonicalized forms below (see
--   `bkar_formula_forestIndex_cube_contributions`).
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L294-L304
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L294-L304

import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Definitions.Def_BKAR_Formula
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.bkar_formula_grown_forest_cube_sectors
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ∀ choices : Forest.ActiveExtensionChoice V,
      ρ oneConfig =
        Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (Forest.edgeSetOrders I.edges).attach
            (fun order =>
              (Forest.grownForestForSupportOrder choices I order).orderedCubeSectorContribution
                order.val ρ)) := by sorry
