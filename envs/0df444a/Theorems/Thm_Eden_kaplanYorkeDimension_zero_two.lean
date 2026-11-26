-- Prove2me | Theorems.Thm_Eden_kaplanYorkeDimension_zero_two
-- name    : Eden.kaplanYorkeDimension_zero_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:42.05205+00:00
-- url     : https://prove2.me/theorems/85f45a2c-ad79-5620-abcc-24b617626a36
-- title:
--   Eden: kaplan Yorke Dimension zero two
-- statement:
--   The Eden construction uses the kaplan Yorke Dimension zero two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L35-L44
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L35-L44

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.kaplanYorkeDimension_zero_two {c : ℝ} (hc : 4 < c) :
    kaplanYorkeDimension ![0, -2, -2, -4, -c] = 1 := by sorry
