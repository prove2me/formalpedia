-- Prove2me | Theorems.Thm_BKAR_canonicalGrownForestForSupport_cubeContribution_eq_sum_edgeSetOrders
-- name    : BKAR.canonicalGrownForestForSupport_cubeContribution_eq_sum_edgeSetOrders
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:08:00.18528+00:00
-- url     : https://prove2.me/theorems/27d10ce3-aebf-47f4-bbe7-a92041be1b12
-- title:
--   BKAR: canonical Grown Forest For Support cube Contribution eq sum edge Set Orders
-- statement:
--   For a fixed choice system and support, the canonical grown representative's
--   usual cube contribution is exactly the sum over all ordered sectors of that
--   same representative.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L224-L235
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L224-L235

import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Definitions.Def_BKAR_Formula
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.canonicalGrownForestForSupport_cubeContribution_eq_sum_edgeSetOrders
    (choices : Forest.ActiveExtensionChoice V)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    (Forest.canonicalGrownForestForSupport choices I).cubeContribution ρ =
      Finset.sum (Forest.edgeSetOrders I.edges)
        (fun order =>
          (Forest.canonicalGrownForestForSupport choices I).orderedCubeSectorContribution
            order ρ) := by sorry
