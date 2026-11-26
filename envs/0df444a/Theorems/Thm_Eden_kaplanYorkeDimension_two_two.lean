-- Prove2me | Theorems.Thm_Eden_kaplanYorkeDimension_two_two
-- name    : Eden.kaplanYorkeDimension_two_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:03.606321+00:00
-- url     : https://prove2.me/theorems/3fa4a754-2a4f-4bd2-a21d-27c2ae4bada9
-- title:
--   Eden: kaplan Yorke Dimension two two
-- statement:
--   The Eden construction uses the kaplan Yorke Dimension two two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L72-L82
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L72-L82

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.kaplanYorkeDimension_two_two {c : ℝ} (hc : 4 < c) :
    kaplanYorkeDimension ![0, 0, -4, -4, -c] = 2 := by sorry
