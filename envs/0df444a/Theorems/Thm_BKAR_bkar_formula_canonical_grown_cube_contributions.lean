-- Prove2me | Theorems.Thm_BKAR_bkar_formula_canonical_grown_cube_contributions
-- name    : BKAR.bkar_formula_canonical_grown_cube_contributions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:09:23.563134+00:00
-- url     : https://prove2.me/theorems/45b01045-e5de-4e75-b840-691c8370ea31
-- title:
--   BKAR: bkar formula canonical grown cube contributions
-- statement:
--   Public folded canonical-representative cube-contribution BKAR form. This is the
--   support-indexed sum, modulo the still-explicit choice of `Forest`
--   representatives used to realize each abstract forest support.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L323-L330
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L323-L330

import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Definitions.Def_BKAR_Formula
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.bkar_formula_canonical_grown_cube_contributions
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ∀ choices : Forest.ActiveExtensionChoice V,
      ρ oneConfig = canonicalGrownForestCubeContributionSum choices ρ := by sorry
