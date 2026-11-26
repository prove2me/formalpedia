-- Prove2me | Theorems.Thm_Eden_periodicGlobalLogGrowth_eq
-- name    : Eden.periodicGlobalLogGrowth_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:40:04.896742+00:00
-- url     : https://prove2.me/theorems/804d775a-f85f-5c77-ad87-c4812bba0040
-- title:
--   Eden: periodic Global Log Growth eq
-- statement:
--   The logarithmic spatial supremum is linear in every nonnegative real time.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean#L106-L110
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean#L106-L110

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_PeriodicGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.periodicGlobalLogGrowth_eq {c t : ℝ} (hc : 4 < c) (ht : 0 ≤ t)
    {k : ℕ} (hk : k ≤ 5) :
    periodicGlobalLogGrowth c k t = t * spectrumPartialSum ![2, 0, -2, -2, -c] k := by sorry
