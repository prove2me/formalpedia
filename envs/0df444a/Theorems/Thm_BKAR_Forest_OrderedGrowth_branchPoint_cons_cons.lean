-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_cons_cons
-- name    : BKAR.Forest.OrderedGrowth.branchPoint_cons_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:38:46.66665+00:00
-- url     : https://prove2.me/theorems/5526989b-75ea-456e-8704-130e9e4b2cae
-- title:
--   Ordered Growth: branch Point cons cons
-- statement:
--   The Ordered Growth construction uses the branch Point cons cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L105-L111
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L105-L111

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

theorem BKAR.Forest.OrderedGrowth.branchPoint_cons_cons {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ)
    (t : ℝ) (ts : List ℝ) :
    (OrderedGrowth.cons step tail).branchPoint u (t :: ts) =
      tail.branchPoint (step.extendParam u t) ts := by sorry
