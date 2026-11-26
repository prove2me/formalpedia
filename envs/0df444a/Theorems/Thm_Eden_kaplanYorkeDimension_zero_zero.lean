-- Prove2me | Theorems.Thm_Eden_kaplanYorkeDimension_zero_zero
-- name    : Eden.kaplanYorkeDimension_zero_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:35.834986+00:00
-- url     : https://prove2.me/theorems/0ec00eb4-dab8-5900-bcc2-35cdcf318652
-- title:
--   Eden: kaplan Yorke Dimension zero zero
-- statement:
--   The Eden construction uses the kaplan Yorke Dimension zero zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L14-L21
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L14-L21

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.kaplanYorkeDimension_zero_zero {c : ℝ} (hc : 4 < c) :
    kaplanYorkeDimension ![-2, -2, -2, -2, -c] = 0 := by sorry
