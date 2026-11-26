-- Prove2me | Theorems.Thm_Eden_supremumSingularProduct_pos
-- name    : Eden.supremumSingularProduct_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:39:02.628415+00:00
-- url     : https://prove2.me/theorems/e2ab0eaa-9086-4c0e-b82b-83c0970e139c
-- title:
--   Eden: supremum Singular Product pos
-- statement:
--   The Eden construction uses the supremum Singular Product pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L48-L50
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L48-L50

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.supremumSingularProduct_pos {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) : 0 < supremumSingularProduct c k t := by sorry
