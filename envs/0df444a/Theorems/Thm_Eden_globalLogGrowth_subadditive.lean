-- Prove2me | Theorems.Thm_Eden_globalLogGrowth_subadditive
-- name    : Eden.globalLogGrowth_subadditive
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:39:30.820432+00:00
-- url     : https://prove2.me/theorems/fbb9e337-3214-424f-9500-8f30510ca620
-- title:
--   Eden: global Log Growth subadditive
-- statement:
--   The function G_k is subadditive through all nonnegative real times.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L84-L91
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L84-L91

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.globalLogGrowth_subadditive {k : ℕ} (hk : k ≤ 5) {c s t : ℝ}
    (hc : 4 ≤ c) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    globalLogGrowth c k (s + t) ≤ globalLogGrowth c k s + globalLogGrowth c k t := by sorry
