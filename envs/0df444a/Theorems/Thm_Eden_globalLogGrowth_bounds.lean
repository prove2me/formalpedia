-- Prove2me | Theorems.Thm_Eden_globalLogGrowth_bounds
-- name    : Eden.globalLogGrowth_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:38:34.335003+00:00
-- url     : https://prove2.me/theorems/2debe479-0c5e-4440-84eb-6d85695386b1
-- title:
--   Eden: global Log Growth bounds
-- statement:
--   The Eden construction uses the global Log Growth bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L93-L100
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L93-L100

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.globalLogGrowth_bounds {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) :
    (k : ℝ) * (-c * t) ≤ globalLogGrowth c k t ∧ globalLogGrowth c k t ≤ (k : ℝ) * (3 * t) := by sorry
