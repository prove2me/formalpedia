-- Prove2me | Theorems.Thm_Eden_exists_globalLogGrowth_linear_bound
-- name    : Eden.exists_globalLogGrowth_linear_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:39:12.577247+00:00
-- url     : https://prove2.me/theorems/571cae0f-e749-5d3f-afa0-3a472a677a8f
-- title:
--   Eden: exists global Log Growth linear bound
-- statement:
--   An explicit finite constant works uniformly for every nonnegative real time.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L110-L113
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L110-L113

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exists_globalLogGrowth_linear_bound {k : ℕ} (hk : k ≤ 5) {c : ℝ} (hc : 4 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → |globalLogGrowth c k t| ≤ C * t := by sorry
