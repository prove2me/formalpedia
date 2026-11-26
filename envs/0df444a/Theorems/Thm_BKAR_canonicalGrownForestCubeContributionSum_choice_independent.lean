-- Prove2me | Theorems.Thm_BKAR_canonicalGrownForestCubeContributionSum_choice_independent
-- name    : BKAR.canonicalGrownForestCubeContributionSum_choice_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:07:44.083443+00:00
-- url     : https://prove2.me/theorems/4a9d69cb-3c42-53e4-a7fd-20abddc568d0
-- title:
--   BKAR: canonical Grown Forest Cube Contribution Sum choice independent
-- statement:
--   The folded canonical grown-representative cube contribution sum is also independent
--   of the auxiliary active-extension choices.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L210-L217
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L210-L217

import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Definitions.Def_BKAR_Formula
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.canonicalGrownForestCubeContributionSum_choice_independent
    (choices₁ choices₂ : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    canonicalGrownForestCubeContributionSum choices₁ ρ =
      canonicalGrownForestCubeContributionSum choices₂ ρ := by sorry
