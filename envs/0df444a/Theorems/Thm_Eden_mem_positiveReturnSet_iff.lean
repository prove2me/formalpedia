-- Prove2me | Theorems.Thm_Eden_mem_positiveReturnSet_iff
-- name    : Eden.mem_positiveReturnSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:38.396479+00:00
-- url     : https://prove2.me/theorems/9ec85b16-9fbd-5385-87ab-d93e393739cd
-- title:
--   Eden: mem positive Return Set iff
-- statement:
--   Every positive-return point is the origin or lies on exactly one of the four
--   circles; the converse supplies explicit positive return times.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicSets.lean#L112-L135
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicSets.lean#L112-L135

import Definitions.Def_Eden_RotationReturns
import Definitions.Def_Eden_PeriodicSets
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.mem_positiveReturnSet_iff {c : ℝ} (hc : 0 < c) (p : PhaseSpace) :
    p ∈ positiveReturnSet c ↔ p = 0 ∨ p ∈ firstCircle 1 ∨ p ∈ firstCircle 2 ∨
      p ∈ secondCircle 1 ∨ p ∈ secondCircle 2 := by sorry
