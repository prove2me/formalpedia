-- Prove2me | Theorems.Thm_Eden_integerGrowthValues_bddAbove
-- name    : Eden.integerGrowthValues_bddAbove
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:38:51.05953+00:00
-- url     : https://prove2.me/theorems/32ccaeef-b2c5-45e2-b192-7037eb76e3ef
-- title:
--   Eden: integer Growth Values bdd Above
-- statement:
--   The Eden construction uses the integer Growth Values bdd Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L30-L34
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L30-L34

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.integerGrowthValues_bddAbove {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) : BddAbove (integerGrowthValues c k t) := by sorry
