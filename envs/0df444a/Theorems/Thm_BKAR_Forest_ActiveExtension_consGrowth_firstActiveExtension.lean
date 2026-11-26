-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_consGrowth_firstActiveExtension
-- name    : BKAR.Forest.ActiveExtension.consGrowth_firstActiveExtension
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:44:31.3418+00:00
-- url     : https://prove2.me/theorems/4367a80c-6e8f-4e46-a1f9-80489c1fa3ac
-- title:
--   Active Extension: cons Growth first Active Extension
-- statement:
--   The Active Extension construction uses the cons Growth first Active Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L43-L46
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L43-L46

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

theorem BKAR.Forest.ActiveExtension.consGrowth_firstActiveExtension (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G) :
    (h.consGrowth tail).firstActiveExtension = h := by sorry
