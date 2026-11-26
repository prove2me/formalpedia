-- Prove2me | Theorems.Thm_Eden_kaplanYorkeDimension_one_two
-- name    : Eden.kaplanYorkeDimension_one_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:53:09.594522+00:00
-- url     : https://prove2.me/theorems/7cb11e87-8872-4593-a41d-ca634bac4c8c
-- title:
--   Eden: kaplan Yorke Dimension one two
-- statement:
--   The Eden construction uses the kaplan Yorke Dimension one two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L60-L70
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L60-L70

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.kaplanYorkeDimension_one_two {c : ℝ} (hc : 4 < c) :
    kaplanYorkeDimension ![2, 0, 0, -4, -c] = 7 / 2 := by sorry
