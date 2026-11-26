-- Prove2me | Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_branchIntegral_eq_orderedContribution
-- name    : BKAR.Forest.canonicalGrownForestForSupport_branchIntegral_eq_orderedContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:04:24.323806+00:00
-- url     : https://prove2.me/theorems/afebc5cc-1357-4e83-9dc1-d4a395f16eb0
-- title:
--   Forest: canonical Grown Forest For Support branch Integral eq ordered Contribution
-- statement:
--   The canonical support representative's canonical-order contribution is the
--   branch integral of its concrete ordered-growth certificate.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean#L163-L171
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean#L163-L171

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.canonicalGrownForestForSupport_branchIntegral_eq_orderedContribution
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) :
  (canonicalGrownForestForSupport_orderedGrowth choices I).branchIntegral
        emptyParam ρ =
      (canonicalGrownForestForSupport choices I).orderedContribution
        I.canonicalOrder.val ρ := by sorry
