-- Prove2me | Theorems.Thm_Eden_normalizedLogSingularValues_periodic_le_unit
-- name    : Eden.normalizedLogSingularValues_periodic_le_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:40:09.288396+00:00
-- url     : https://prove2.me/theorems/7d1e11e0-68ad-460d-876f-cb1d287c9401
-- title:
--   Eden: normalized Log Singular Values periodic le unit
-- statement:
--   The Eden construction uses the normalized Log Singular Values periodic le unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean#L16-L35
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean#L16-L35

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_PeriodicGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.normalizedLogSingularValues_periodic_le_unit {c t : ℝ}
    (hc : 4 < c) (ht : 0 < t) {p : PhaseSpace}
    (hp : p ∈ periodicEquilibriumSet c) :
    ∀ i : Fin 5, normalizedLogSingularValues c t p i ≤ ![2, 0, -2, -2, -c] i := by sorry
