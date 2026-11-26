-- Prove2me | Theorems.Thm_Eden_supremumSingularProduct_four_five
-- name    : Eden.supremumSingularProduct_four_five
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:40:52.353796+00:00
-- url     : https://prove2.me/theorems/9afaf1c8-9663-4f02-8b51-e500c39fd816
-- title:
--   Eden: supremum Singular Product four five
-- statement:
--   Sharp spatial suprema for k=4,5, valid at every nonnegative real time.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L17-L35
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExactGlobalGrowth.lean#L17-L35

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.supremumSingularProduct_four_five {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {k : ℕ} (hk₄ : 4 ≤ k) (hk₅ : k ≤ 5) :
    supremumSingularProduct c k t =
      Real.exp (4 * t - c * t * ((k : ℝ) - 4)) := by sorry
