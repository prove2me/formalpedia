-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_singletonGrowth_eq_consGrowth_nil
-- name    : BKAR.Forest.ActiveExtension.singletonGrowth_eq_consGrowth_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:44:33.2096+00:00
-- url     : https://prove2.me/theorems/bd6224f5-f5a4-57c2-9a3a-dff827e6a5cc
-- title:
--   Active Extension: singleton Growth eq cons Growth nil
-- statement:
--   The Active Extension construction uses the singleton Growth eq cons Growth nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L53-L55
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L53-L55

import Definitions.Def_BKAR_OrderedTerminal
import Definitions.Def_BKAR_OrderedRecursion
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.ActiveExtension.singletonGrowth_eq_consGrowth_nil (h : ActiveExtension F e) :
    h.singletonGrowth = h.consGrowth (OrderedGrowth.nil h.forest) := by sorry
