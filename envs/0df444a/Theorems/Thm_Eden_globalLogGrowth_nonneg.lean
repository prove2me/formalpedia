-- Prove2me | Theorems.Thm_Eden_globalLogGrowth_nonneg
-- name    : Eden.globalLogGrowth_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:41:36.300801+00:00
-- url     : https://prove2.me/theorems/d4f80ff1-817f-4dda-9c23-67cf92602f38
-- title:
--   Eden: global Log Growth nonneg
-- statement:
--   The Eden construction uses the global Log Growth nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L90-L95
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L90-L95

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.globalLogGrowth_nonneg {k : ℕ} (hk : k ≤ 4) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) : 0 ≤ globalLogGrowth c k t := by sorry
