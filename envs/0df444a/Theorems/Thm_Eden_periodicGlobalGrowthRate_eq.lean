-- Prove2me | Theorems.Thm_Eden_periodicGlobalGrowthRate_eq
-- name    : Eden.periodicGlobalGrowthRate_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:37:12.85438+00:00
-- url     : https://prove2.me/theorems/f581d09a-f14d-5ccd-89e8-87e35941b680
-- title:
--   Eden: periodic Global Growth Rate eq
-- statement:
--   The Eden construction uses the periodic Global Growth Rate eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean#L120-L122
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean#L120-L122

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_PeriodicGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.periodicGlobalGrowthRate_eq {c : ℝ} (hc : 4 < c) {k : ℕ} (hk : k ≤ 5) :
    periodicGlobalGrowthRate c k = spectrumPartialSum ![2, 0, -2, -2, -c] k := by sorry
