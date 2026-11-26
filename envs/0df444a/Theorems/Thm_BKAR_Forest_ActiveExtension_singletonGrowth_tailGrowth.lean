-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_singletonGrowth_tailGrowth
-- name    : BKAR.Forest.ActiveExtension.singletonGrowth_tailGrowth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:40:23.442696+00:00
-- url     : https://prove2.me/theorems/08803366-8c5f-4667-a2ce-5a994c94ea85
-- title:
--   Active Extension: singleton Growth tail Growth
-- statement:
--   The Active Extension construction uses the singleton Growth tail Growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminal.lean#L35-L37
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminal.lean#L35-L37

import Definitions.Def_BKAR_OrderedBranch
import Definitions.Def_BKAR_OrderedTerminal
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F : Forest V} {e : Edge V}

theorem BKAR.Forest.ActiveExtension.singletonGrowth_tailGrowth (h : ActiveExtension F e) :
    h.singletonGrowth.tailGrowth = OrderedGrowth.nil h.forest := by sorry
