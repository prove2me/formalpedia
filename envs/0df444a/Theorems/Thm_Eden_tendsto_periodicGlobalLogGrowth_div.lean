-- Prove2me | Theorems.Thm_Eden_tendsto_periodicGlobalLogGrowth_div
-- name    : Eden.tendsto_periodicGlobalLogGrowth_div
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:40:04.700975+00:00
-- url     : https://prove2.me/theorems/370aec9b-4990-5baa-9463-a7457043e876
-- title:
--   Eden: tendsto periodic Global Log Growth div
-- statement:
--   The Eden construction uses the tendsto periodic Global Log Growth div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean#L112-L118
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean#L112-L118

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_PeriodicGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.tendsto_periodicGlobalLogGrowth_div {c : ℝ} (hc : 4 < c)
    {k : ℕ} (hk : k ≤ 5) :
    Tendsto (fun t : ℝ => periodicGlobalLogGrowth c k t / t) atTop
      (𝓝 (spectrumPartialSum ![2, 0, -2, -2, -c] k)) := by sorry
