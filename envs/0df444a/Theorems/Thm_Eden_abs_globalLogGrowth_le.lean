-- Prove2me | Theorems.Thm_Eden_abs_globalLogGrowth_le
-- name    : Eden.abs_globalLogGrowth_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:05.843817+00:00
-- url     : https://prove2.me/theorems/b6275541-6cf5-54a1-aae4-2ff7bba26925
-- title:
--   Eden: abs global Log Growth le
-- statement:
--   The Eden construction uses the abs global Log Growth le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L102-L107
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L102-L107

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.abs_globalLogGrowth_le {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) : |globalLogGrowth c k t| ≤ ((k : ℝ) * c) * t := by sorry
