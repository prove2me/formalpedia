-- Prove2me | Theorems.Thm_Eden_globalGrowthRate_nonneg
-- name    : Eden.globalGrowthRate_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:49:25.149165+00:00
-- url     : https://prove2.me/theorems/93bc2bc2-e9d0-4ce6-997a-6c8e0f35af36
-- title:
--   Eden: global Growth Rate nonneg
-- statement:
--   The Eden construction uses the global Growth Rate nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L97-L101
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L97-L101

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.globalGrowthRate_nonneg {k : ℕ} (hk : k ≤ 4) {c : ℝ} (hc : 4 ≤ c) :
    0 ≤ globalGrowthRate c k := by sorry
