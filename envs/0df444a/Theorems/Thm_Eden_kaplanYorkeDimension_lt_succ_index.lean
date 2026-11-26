-- Prove2me | Theorems.Thm_Eden_kaplanYorkeDimension_lt_succ_index
-- name    : Eden.kaplanYorkeDimension_lt_succ_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:56:40.235849+00:00
-- url     : https://prove2.me/theorems/34169ada-5133-58e8-be8a-06c0a7a13e62
-- title:
--   Eden: kaplan Yorke Dimension lt succ index
-- statement:
--   The Eden construction uses the kaplan Yorke Dimension lt succ index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationSign.lean#L57-L62
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationSign.lean#L57-L62

import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_InterpolationSign
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.kaplanYorkeDimension_lt_succ_index {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a < 5) :
    kaplanYorkeDimension a < (kaplanYorkeIndex a : ℝ) + 1 := by sorry
