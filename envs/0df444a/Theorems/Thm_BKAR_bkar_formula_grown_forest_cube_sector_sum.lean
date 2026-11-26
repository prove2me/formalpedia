-- Prove2me | Theorems.Thm_BKAR_bkar_formula_grown_forest_cube_sector_sum
-- name    : BKAR.bkar_formula_grown_forest_cube_sector_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:08:32.889878+00:00
-- url     : https://prove2.me/theorems/b455c00e-c730-567c-aa52-71eaad124d24
-- title:
--   BKAR: bkar formula grown forest cube sector sum
-- statement:
--   Public compact grown-representative closed-sector form. The accompanying theorem
--   `grownForestCubeSectorSum_choice_independent` proves that the right-hand
--   side is independent of the auxiliary active-extension choices.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L311-L316
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L311-L316

import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Definitions.Def_BKAR_Formula
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.bkar_formula_grown_forest_cube_sector_sum
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ∀ choices : Forest.ActiveExtensionChoice V,
      ρ oneConfig = grownForestCubeSectorSum choices ρ := by sorry
