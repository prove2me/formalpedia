-- Prove2me | Theorems.Thm_Eden_periodic_dimension_conventions_distinct
-- name    : Eden.periodic_dimension_conventions_distinct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:43:31.343386+00:00
-- url     : https://prove2.me/theorems/c697b4bd-aa94-5e4d-918d-0f05206b9a8e
-- title:
--   Eden: periodic dimension conventions distinct
-- statement:
--   The Eden construction uses the periodic dimension conventions distinct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L101-L106
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L101-L106

import Definitions.Def_Eden_CommonIndex
import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_CommonIndexPeriodic
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.periodic_dimension_conventions_distinct {c : ℝ} (hc : 4 < c) :
    sSup (asymptoticDimension c '' periodicEquilibriumSet c) <
      sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) := by sorry
