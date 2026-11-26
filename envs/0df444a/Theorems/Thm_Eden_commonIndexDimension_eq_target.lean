-- Prove2me | Theorems.Thm_Eden_commonIndexDimension_eq_target
-- name    : Eden.commonIndexDimension_eq_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:06:06.917806+00:00
-- url     : https://prove2.me/theorems/9a0cedb0-bb4d-4401-8090-410f72a40636
-- title:
--   Eden: common Index Dimension eq target
-- statement:
--   The common-index dimension on the full attractor is exactly 4+4/c.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndex.lean#L69-L72
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndex.lean#L69-L72

import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_CommonIndex
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.commonIndexDimension_eq_target {c : ℝ} (hc : 4 < c) :
    commonIndexDimension c = 4 + 4 / c := by sorry
