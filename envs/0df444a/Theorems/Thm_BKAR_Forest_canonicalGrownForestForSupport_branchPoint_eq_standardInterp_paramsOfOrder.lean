-- Prove2me | Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_branchPoint_eq_standardInterp_paramsOfOrder
-- name    : BKAR.Forest.canonicalGrownForestForSupport_branchPoint_eq_standardInterp_paramsOfOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:03:52.693313+00:00
-- url     : https://prove2.me/theorems/1ead6236-3858-4b27-883f-67e868d3fb6f
-- title:
--   Forest: canonical Grown Forest For Support branch Point eq standard Interp params Of Order
-- statement:
--   The branch point attached to the canonical support representative is exactly
--   its standard interpolation in canonical-order coordinates.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean#L177-L187
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean#L177-L187

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.canonicalGrownForestForSupport_branchPoint_eq_standardInterp_paramsOfOrder
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ts : List ℝ) (hlen : ts.length = I.canonicalOrder.val.length) :
    (canonicalGrownForestForSupport_orderedGrowth choices I).branchPoint
        emptyParam ts =
      (canonicalGrownForestForSupport choices I).standardInterp
        ((canonicalGrownForestForSupport choices I).paramsOfOrder
          I.canonicalOrder.val ts) := by sorry
