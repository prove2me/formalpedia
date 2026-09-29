-- Prove2me | Theorems.Thm_Chou_not_hasExponentialGrowth_of_isExponentiallyBounded
-- name    : Chou.not_hasExponentialGrowth_of_isExponentiallyBounded
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-21T15:34:21.965418+00:00
-- url     : https://prove2.me/theorems/0371f57e-53e3-4a8b-9219-48397a044f71
-- statement:
--   A finitely generated group which is exponentially bounded does not have exponential growth.

import Definitions.Def_Chou_Growth
import Mathlib

namespace Chou

theorem not_hasExponentialGrowth_of_isExponentiallyBounded {G : Type*} [Group G] [Group.FG G] (h : IsExponentiallyBounded G) : ¬ HasExponentialGrowth G := by sorry

end Chou
