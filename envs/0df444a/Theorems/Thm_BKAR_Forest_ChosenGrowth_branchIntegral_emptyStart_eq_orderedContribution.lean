-- Prove2me | Theorems.Thm_BKAR_Forest_ChosenGrowth_branchIntegral_emptyStart_eq_orderedContribution
-- name    : BKAR.Forest.ChosenGrowth.branchIntegral_emptyStart_eq_orderedContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:35.576094+00:00
-- url     : https://prove2.me/theorems/7d4b479f-3a28-4bbf-8359-cffe7d8390cc
-- title:
--   Chosen Growth: branch Integral empty Start eq ordered Contribution
-- statement:
--   Chosen-growth version of
--   `OrderedGrowth.branchIntegral_emptyStart_eq_orderedContribution`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean#L79-L84
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean#L79-L84

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_emptyStart_eq_orderedContribution

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ChosenGrowth
variable {choices : ActiveExtensionChoice V}
variable {G : Forest V} {order : List (Edge V)}

theorem BKAR.Forest.ChosenGrowth.branchIntegral_emptyStart_eq_orderedContribution
    (path : ChosenGrowth choices (Forest.empty V) order G)
    (ρ : (Edge V → ℝ) → ℝ) :
    path.toOrderedGrowth.branchIntegral emptyParam ρ =
      G.orderedContribution order ρ := by sorry
