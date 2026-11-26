-- Prove2me | Theorems.Thm_BKAR_ForestIndex_cubeContribution_eq_canonicalGrownForestForSupport
-- name    : BKAR.ForestIndex.cubeContribution_eq_canonicalGrownForestForSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:03:18.375009+00:00
-- url     : https://prove2.me/theorems/3c2ca847-7687-4402-82ef-fa80fce63cfb
-- title:
--   Forest Index: cube Contribution eq canonical Grown Forest For Support
-- statement:
--   Any concrete active-extension choice system realizes the same abstract
--   forest-index cube contribution.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ForestIndexCube.lean#L43-L53
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ForestIndexCube.lean#L43-L53

import Definitions.Def_BKAR_OrderedAssembly_CubeFold
import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.ForestIndex
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.ForestIndex.cubeContribution_eq_canonicalGrownForestForSupport
    (I : ForestIndex V) (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    I.cubeContribution ρ =
      (Forest.canonicalGrownForestForSupport choices I).cubeContribution ρ := by sorry
