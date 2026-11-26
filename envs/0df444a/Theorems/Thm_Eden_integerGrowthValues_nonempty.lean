-- Prove2me | Theorems.Thm_Eden_integerGrowthValues_nonempty
-- name    : Eden.integerGrowthValues_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:11.455462+00:00
-- url     : https://prove2.me/theorems/69864f5b-c7d9-54c3-862b-1d20e10048cc
-- title:
--   Eden: integer Growth Values nonempty
-- statement:
--   The Eden construction uses the integer Growth Values nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L27-L28
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowth.lean#L27-L28

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.integerGrowthValues_nonempty (c : ℝ) (k : ℕ) (t : ℝ) :
    (integerGrowthValues c k t).Nonempty := by sorry
