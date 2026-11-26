-- Prove2me | Theorems.Thm_Eden_periodicGlobalGrowthIndex_eq_three
-- name    : Eden.periodicGlobalGrowthIndex_eq_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:05:12.856494+00:00
-- url     : https://prove2.me/theorems/265175aa-e1a5-466d-a76f-418b5c128d62
-- title:
--   Eden: periodic Global Growth Index eq three
-- statement:
--   The last nonnegative integer global-sum node is three when c > 4.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalDimension.lean#L58-L65
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalDimension.lean#L58-L65

import Definitions.Def_Eden_PeriodicGlobalGrowth
import Definitions.Def_Eden_PeriodicGlobalDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.periodicGlobalGrowthIndex_eq_three {c : ℝ} (hc : 4 < c) :
    kaplanYorkeIndex (periodicGlobalGrowthIncrements c) = 3 := by sorry
