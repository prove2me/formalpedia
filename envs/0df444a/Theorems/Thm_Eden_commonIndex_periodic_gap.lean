-- Prove2me | Theorems.Thm_Eden_commonIndex_periodic_gap
-- name    : Eden.commonIndex_periodic_gap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:43:38.568343+00:00
-- url     : https://prove2.me/theorems/8c0848dc-3e51-4095-9fc1-f92fd541f96a
-- title:
--   Eden: common Index periodic gap
-- statement:
--   The Eden construction uses the common Index periodic gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L94-L99
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L94-L99

import Definitions.Def_Eden_CommonIndex
import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_CommonIndexPeriodic
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.commonIndex_periodic_gap {c : ℝ} (hc : 4 < c) :
    sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) < commonIndexDimension c := by sorry
