-- Prove2me | Theorems.Thm_Eden_kaplanYorkeDimension_zero_one
-- name    : Eden.kaplanYorkeDimension_zero_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:48.372915+00:00
-- url     : https://prove2.me/theorems/f6593816-a508-4a18-8358-824d7b6426ea
-- title:
--   Eden: kaplan Yorke Dimension zero one
-- statement:
--   The Eden construction uses the kaplan Yorke Dimension zero one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L23-L33
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L23-L33

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.kaplanYorkeDimension_zero_one {c : ℝ} (hc : 4 < c) :
    kaplanYorkeDimension ![2, 0, -2, -2, -c] = 3 := by sorry
