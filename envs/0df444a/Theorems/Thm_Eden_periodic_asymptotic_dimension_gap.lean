-- Prove2me | Theorems.Thm_Eden_periodic_asymptotic_dimension_gap
-- name    : Eden.periodic_asymptotic_dimension_gap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:23:32.151262+00:00
-- url     : https://prove2.me/theorems/47c84aa7-b57e-48cd-96b7-c23b07f4d310
-- title:
--   Eden: periodic asymptotic dimension gap
-- statement:
--   The Eden construction uses the periodic asymptotic dimension gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGap.lean#L47-L53
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGap.lean#L47-L53

import Definitions.Def_Eden_PeriodicDimensions
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_PeriodicGap
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.periodic_asymptotic_dimension_gap {c : ℝ} (hc : 4 < c) :
    sSup (asymptoticDimension c '' periodicEquilibriumSet c) <
      globalLyapunovDimension c attractor := by sorry
