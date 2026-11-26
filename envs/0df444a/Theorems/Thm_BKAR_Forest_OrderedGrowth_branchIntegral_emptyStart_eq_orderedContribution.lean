-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_emptyStart_eq_orderedContribution
-- name    : BKAR.Forest.OrderedGrowth.branchIntegral_emptyStart_eq_orderedContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:29.262094+00:00
-- url     : https://prove2.me/theorems/eefdce72-8f7b-4102-97b9-eaf12a008570
-- title:
--   Ordered Growth: branch Integral empty Start eq ordered Contribution
-- statement:
--   An ordered growth from the empty forest computes the same integral as the
--   ordered contribution of its terminal `Forest` representative in that growth order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean#L57-L66
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean#L57-L66

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_emptyStart_eq_orderedContribution

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {G : Forest V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegral_emptyStart_eq_orderedContribution
    (growth : OrderedGrowth (Forest.empty V) order G)
    (ρ : (Edge V → ℝ) → ℝ) :
    growth.branchIntegral emptyParam ρ =
      G.orderedContribution order ρ := by sorry
