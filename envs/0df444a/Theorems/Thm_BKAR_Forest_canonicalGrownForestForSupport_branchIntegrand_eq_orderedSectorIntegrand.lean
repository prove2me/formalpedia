-- Prove2me | Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_branchIntegrand_eq_orderedSectorIntegrand
-- name    : BKAR.Forest.canonicalGrownForestForSupport_branchIntegrand_eq_orderedSectorIntegrand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:03:58.011746+00:00
-- url     : https://prove2.me/theorems/5ce6298c-9d8d-41db-9b29-22f5958600da
-- title:
--   Forest: canonical Grown Forest For Support branch Integrand eq ordered Sector Integrand
-- statement:
--   The canonical support representative's canonical branch integrand is the
--   usual ordered-sector integrand of that representative, in list simplex
--   coordinates.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean#L194-L206
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean#L194-L206

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.canonicalGrownForestForSupport_branchIntegrand_eq_orderedSectorIntegrand
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ)
    (ts : List ℝ) (hlen : ts.length = I.canonicalOrder.val.length) :
    (canonicalGrownForestForSupport_orderedGrowth choices I).branchIntegrand
        emptyParam ρ ts =
      mixedPartialList I.canonicalOrder.val.reverse ρ
        ((canonicalGrownForestForSupport choices I).standardInterp
          ((canonicalGrownForestForSupport choices I).paramsOfOrder
            I.canonicalOrder.val ts)) := by sorry
