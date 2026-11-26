-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_cons
-- name    : BKAR.Forest.OrderedGrowth.branchIntegral_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:39:57.680963+00:00
-- url     : https://prove2.me/theorems/c5609e18-cb00-45e3-83f0-c93775184783
-- title:
--   Ordered Growth: branch Integral cons
-- statement:
--   The Ordered Growth construction uses the branch Integral cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L303-L312
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L303-L312

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

theorem BKAR.Forest.OrderedGrowth.branchIntegral_cons {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step tail).branchIntegral u ρ =
      ∫ t in 0..(1 : ℝ),
        orderedSimplexIntegralAux t order
          (fun ts =>
            (OrderedGrowth.cons step tail).branchIntegrand u ρ (t :: ts)) := by sorry
