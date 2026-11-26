-- Prove2me | Theorems.Thm_BKAR_bkar_formula_forestIndex_cube_contributions
-- name    : BKAR.bkar_formula_forestIndex_cube_contributions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:03:46.741865+00:00
-- url     : https://prove2.me/theorems/7b5a9dbd-34b6-49a0-a3c6-43baa2bb0e00
-- title:
--   BKAR: bkar formula forest Index cube contributions
-- statement:
--   Main scalar BKAR theorem — the forest interpolation formula: the value at the
--   all-ones configuration is the support-indexed sum of ordinary cube
--   contributions over abstract forest edge sets.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L353-L360
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L353-L360

import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Definitions.Def_BKAR_Formula
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.bkar_formula_forestIndex_cube_contributions
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ρ oneConfig =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => I.cubeContribution ρ) := by sorry
