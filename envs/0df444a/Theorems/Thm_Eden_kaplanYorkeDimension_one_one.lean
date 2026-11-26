-- Prove2me | Theorems.Thm_Eden_kaplanYorkeDimension_one_one
-- name    : Eden.kaplanYorkeDimension_one_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:45.879688+00:00
-- url     : https://prove2.me/theorems/bb6b3a91-5d2c-5035-ada6-9420eeb1cba7
-- title:
--   Eden: kaplan Yorke Dimension one one
-- statement:
--   The Eden construction uses the kaplan Yorke Dimension one one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L46-L58
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L46-L58

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.kaplanYorkeDimension_one_one {c : ℝ} (hc : 4 < c) :
    kaplanYorkeDimension ![2, 2, 0, 0, -c] = targetDimension c := by sorry
