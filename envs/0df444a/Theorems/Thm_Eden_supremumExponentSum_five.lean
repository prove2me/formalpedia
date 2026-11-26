-- Prove2me | Theorems.Thm_Eden_supremumExponentSum_five
-- name    : Eden.supremumExponentSum_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:33.353664+00:00
-- url     : https://prove2.me/theorems/4e1589bf-0e36-563d-bb86-0cd8abdf2c9b
-- title:
--   Eden: supremum Exponent Sum five
-- statement:
--   The Eden construction uses the supremum Exponent Sum five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L127-L128
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L127-L128

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.supremumExponentSum_five {c : ℝ} (hc : 4 < c) :
    supremumExponentSum c 5 = 4 - c := by sorry
