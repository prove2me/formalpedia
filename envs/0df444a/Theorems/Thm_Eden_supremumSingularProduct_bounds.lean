-- Prove2me | Theorems.Thm_Eden_supremumSingularProduct_bounds
-- name    : Eden.supremumSingularProduct_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:21.355774+00:00
-- url     : https://prove2.me/theorems/97e2f54d-14e9-467b-bd49-c2f07d68b20d
-- title:
--   Eden: supremum Singular Product bounds
-- statement:
--   The Eden construction uses the supremum Singular Product bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L36-L46
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L36-L46

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.supremumSingularProduct_bounds {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) :
    Real.exp ((k : ℝ) * (-c * t)) ≤ supremumSingularProduct c k t ∧
      supremumSingularProduct c k t ≤ Real.exp ((k : ℝ) * (3 * t)) := by sorry
