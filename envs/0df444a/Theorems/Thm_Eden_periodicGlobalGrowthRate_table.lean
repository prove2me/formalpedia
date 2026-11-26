-- Prove2me | Theorems.Thm_Eden_periodicGlobalGrowthRate_table
-- name    : Eden.periodicGlobalGrowthRate_table
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:04:02.922846+00:00
-- url     : https://prove2.me/theorems/2889e6ac-8be5-4631-8825-f1481ff03281
-- title:
--   Eden: periodic Global Growth Rate table
-- statement:
--   All six global sums, including the empty sum at index zero.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean#L125-L130
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean#L125-L130

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_PeriodicGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.periodicGlobalGrowthRate_table {c : ℝ} (hc : 4 < c) :
    (fun k : Fin 6 => periodicGlobalGrowthRate c k) = ![0, 2, 2, 0, -2, -2 - c] := by sorry
