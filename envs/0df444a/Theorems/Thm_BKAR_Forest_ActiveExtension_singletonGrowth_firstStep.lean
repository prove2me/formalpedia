-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_singletonGrowth_firstStep
-- name    : BKAR.Forest.ActiveExtension.singletonGrowth_firstStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:40:45.343793+00:00
-- url     : https://prove2.me/theorems/b3bf0cb9-a4cd-4167-9e73-d6578520baa4
-- title:
--   Active Extension: singleton Growth first Step
-- statement:
--   The Active Extension construction uses the singleton Growth first Step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminal.lean#L31-L33
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminal.lean#L31-L33

import Definitions.Def_BKAR_OrderedBranch
import Definitions.Def_BKAR_OrderedTerminal
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F : Forest V} {e : Edge V}

theorem BKAR.Forest.ActiveExtension.singletonGrowth_firstStep (h : ActiveExtension F e) :
    h.singletonGrowth.firstStep = h.extension := by sorry
