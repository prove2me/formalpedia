-- Prove2me | Theorems.Thm_Eden_supremum_finiteTimeDimension_periodic
-- name    : Eden.supremum_finiteTimeDimension_periodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:49.421592+00:00
-- url     : https://prove2.me/theorems/5dd51390-6444-48ed-b9d8-b865933807f1
-- title:
--   Eden: supremum finite Time Dimension periodic
-- statement:
--   The Eden construction uses the supremum finite Time Dimension periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGap.lean#L43-L45
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGap.lean#L43-L45

import Definitions.Def_Eden_PeriodicDimensions
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_PeriodicGap
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.supremum_finiteTimeDimension_periodic {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    sSup (finiteTimeDimension c t '' periodicEquilibriumSet c) = 3 := by sorry
