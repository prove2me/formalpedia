-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_consGrowth_tailForest
-- name    : BKAR.Forest.ActiveExtension.consGrowth_tailForest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:44:22.865804+00:00
-- url     : https://prove2.me/theorems/a26968e6-5e70-53d2-a8b6-e00488eb3dea
-- title:
--   Active Extension: cons Growth tail Forest
-- statement:
--   The Active Extension construction uses the cons Growth tail Forest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L48-L51
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L48-L51

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

theorem BKAR.Forest.ActiveExtension.consGrowth_tailForest (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G) :
    (h.consGrowth tail).tailForest = h.forest := by sorry
