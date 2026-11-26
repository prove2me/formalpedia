-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_growth_derivativeOrder
-- name    : BKAR.Forest.TerminalGrowth.growth_derivativeOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:22:30.406577+00:00
-- url     : https://prove2.me/theorems/a01ec060-6eeb-552e-99a1-36dd8b2827da
-- title:
--   Terminal Growth: growth derivative Order
-- statement:
--   The Terminal Growth construction uses the growth derivative Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L97-L99
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L97-L99

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_ActiveBranchData_growth_derivativeOrder

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.growth_derivativeOrder (data : TerminalGrowth F) :
    data.growth.derivativeOrder = data.order.reverse := by sorry
