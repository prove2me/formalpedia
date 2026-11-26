-- Prove2me | Theorems.Thm_Eden_supremumSingularProduct_zero
-- name    : Eden.supremumSingularProduct_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:39:31.432063+00:00
-- url     : https://prove2.me/theorems/3e8bd23a-d7f2-495c-b7df-41e1cf6b303d
-- title:
--   Eden: supremum Singular Product zero
-- statement:
--   The Eden construction uses the supremum Singular Product zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L57-L61
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L57-L61

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.supremumSingularProduct_zero {k : ℕ} (hk : k ≤ 5) {c : ℝ} (hc : 4 ≤ c) :
    supremumSingularProduct c k 0 = 1 := by sorry
