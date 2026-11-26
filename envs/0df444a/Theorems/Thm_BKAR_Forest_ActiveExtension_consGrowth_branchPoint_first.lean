-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_consGrowth_branchPoint_first
-- name    : BKAR.Forest.ActiveExtension.consGrowth_branchPoint_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:35:44.81044+00:00
-- url     : https://prove2.me/theorems/2e2d2c95-2a8d-53cf-9e84-a5c80e044fdd
-- title:
--   Active Extension: cons Growth branch Point first
-- statement:
--   The Active Extension construction uses the cons Growth branch Point first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L65-L69
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L65-L69

import Definitions.Def_BKAR_OrderedTerminal
import Definitions.Def_BKAR_OrderedRecursion
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.ActiveExtension.consGrowth_branchPoint_first (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G)
    (u : F.EdgeParam → ℝ) (t : ℝ) (ts : List ℝ) :
    (h.consGrowth tail).branchPoint u (t :: ts) e = t := by sorry
