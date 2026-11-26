-- Prove2me | Theorems.Thm_Eden_supremumSingularProduct_add_le
-- name    : Eden.supremumSingularProduct_add_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:38:47.267774+00:00
-- url     : https://prove2.me/theorems/7b42abe3-50cf-5c19-ac32-ff94f9520055
-- title:
--   Eden: supremum Singular Product add le
-- statement:
--   Spatial suprema remain over A at the intermediate base point of the cocycle.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L68-L81
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L68-L81

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.supremumSingularProduct_add_le {k : ℕ} (hk : k ≤ 5) {c s t : ℝ}
    (hc : 4 ≤ c) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    supremumSingularProduct c k (s + t) ≤ supremumSingularProduct c k s * supremumSingularProduct c k t := by sorry
