-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_cons_nil
-- name    : BKAR.Forest.OrderedGrowth.branchPoint_cons_nil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:37:58.135829+00:00
-- url     : https://prove2.me/theorems/891f05f6-7d99-5021-bf4c-7686349ad2c2
-- title:
--   Ordered Growth: branch Point cons nil
-- statement:
--   The Ordered Growth construction uses the branch Point cons nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L98-L103
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L98-L103

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchPoint_cons_nil {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ) :
    (OrderedGrowth.cons step tail).branchPoint u [] =
      tail.branchPoint (step.extendParam u 0) [] := by sorry
