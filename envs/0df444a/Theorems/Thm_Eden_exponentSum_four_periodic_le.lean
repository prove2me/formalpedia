-- Prove2me | Theorems.Thm_Eden_exponentSum_four_periodic_le
-- name    : Eden.exponentSum_four_periodic_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:07:05.537518+00:00
-- url     : https://prove2.me/theorems/1298544b-67cc-580f-b413-d2cd61472975
-- title:
--   Eden: exponent Sum four periodic le
-- statement:
--   The Eden construction uses the exponent Sum four periodic le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L52-L60
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L52-L60

import Definitions.Def_Eden_CommonIndex
import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_CommonIndexPeriodic
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exponentSum_four_periodic_le {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ periodicEquilibriumSet c) : spectrumPartialSum (lyapunovExponent c p) 4 ≤ -2 := by sorry
