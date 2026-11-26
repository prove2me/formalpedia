-- Prove2me | Theorems.Thm_Eden_commonIndexLocalDimension_isGreatest
-- name    : Eden.commonIndexLocalDimension_isGreatest
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:32:19.286704+00:00
-- url     : https://prove2.me/theorems/dd1c2efe-9ccb-40ff-af0a-7fd38bf7871e
-- title:
--   Eden: common Index Local Dimension is Greatest
-- statement:
--   The Eden construction uses the common Index Local Dimension is Greatest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndex.lean#L80-L87
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndex.lean#L80-L87

import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_CommonIndex
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.commonIndexLocalDimension_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest (commonIndexLocalDimension c '' attractor) (4 + 4 / c) := by sorry
