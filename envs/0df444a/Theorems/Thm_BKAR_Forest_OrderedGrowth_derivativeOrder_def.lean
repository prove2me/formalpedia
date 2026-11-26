-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_def
-- name    : BKAR.Forest.OrderedGrowth.derivativeOrder_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:47.929118+00:00
-- url     : https://prove2.me/theorems/3d81b666-69ab-592f-bbae-823ba66f6b4b
-- title:
--   Ordered Growth: derivative Order def
-- statement:
--   The Ordered Growth construction uses the derivative Order def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L66-L68
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L66-L68

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.derivativeOrder_def (h : OrderedGrowth F order G) :
    h.derivativeOrder = order.reverse := by sorry
