-- Prove2me | Theorems.Thm_Eden_commonIndex_eq_four
-- name    : Eden.commonIndex_eq_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:04:13.871087+00:00
-- url     : https://prove2.me/theorems/5e11579c-0820-480c-9631-00a90d8902d9
-- title:
--   Eden: common Index eq four
-- statement:
--   The Eden construction uses the common Index eq four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndex.lean#L34-L35
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndex.lean#L34-L35

import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_CommonIndex
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.commonIndex_eq_four {c : ℝ} (hc : 4 < c) : commonIndex c = 4 := by sorry
