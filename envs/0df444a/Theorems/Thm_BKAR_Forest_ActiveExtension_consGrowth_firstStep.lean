-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_consGrowth_firstStep
-- name    : BKAR.Forest.ActiveExtension.consGrowth_firstStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:42:20.669284+00:00
-- url     : https://prove2.me/theorems/d7e94a3f-1e38-453b-9a41-e7ea66a3df6f
-- title:
--   Active Extension: cons Growth first Step
-- statement:
--   The Active Extension construction uses the cons Growth first Step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L33-L36
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L33-L36

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

theorem BKAR.Forest.ActiveExtension.consGrowth_firstStep (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G) :
    (h.consGrowth tail).firstStep = h.extension := by sorry
