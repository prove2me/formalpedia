-- Prove2me | Theorems.Thm_Eden_exponentSum_four_periodic_isGreatest
-- name    : Eden.exponentSum_four_periodic_isGreatest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:08:02.248832+00:00
-- url     : https://prove2.me/theorems/055d56cd-6c19-407a-9382-d80fbd2e3ca6
-- title:
--   Eden: exponent Sum four periodic is Greatest
-- statement:
--   The Eden construction uses the exponent Sum four periodic is Greatest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L62-L71
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndexPeriodic.lean#L62-L71

import Definitions.Def_Eden_CommonIndex
import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_CommonIndexPeriodic
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exponentSum_four_periodic_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest ((fun p => spectrumPartialSum (lyapunovExponent c p) 4) ''
      periodicEquilibriumSet c) (-2) := by sorry
