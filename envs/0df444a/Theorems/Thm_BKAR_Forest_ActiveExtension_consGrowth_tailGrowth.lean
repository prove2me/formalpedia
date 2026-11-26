-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_consGrowth_tailGrowth
-- name    : BKAR.Forest.ActiveExtension.consGrowth_tailGrowth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:43:51.85485+00:00
-- url     : https://prove2.me/theorems/1df41aab-aaeb-54a1-bef4-f60c7ee29f01
-- title:
--   Active Extension: cons Growth tail Growth
-- statement:
--   The Active Extension construction uses the cons Growth tail Growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L38-L41
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L38-L41

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

theorem BKAR.Forest.ActiveExtension.consGrowth_tailGrowth (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G) :
    (h.consGrowth tail).tailGrowth = tail := by sorry
