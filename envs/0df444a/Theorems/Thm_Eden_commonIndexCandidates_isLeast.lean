-- Prove2me | Theorems.Thm_Eden_commonIndexCandidates_isLeast
-- name    : Eden.commonIndexCandidates_isLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:04:39.872373+00:00
-- url     : https://prove2.me/theorems/2afc98cd-3645-48ca-aaa5-29b52c077b40
-- title:
--   Eden: common Index Candidates is Least
-- statement:
--   The Eden construction uses the common Index Candidates is Least property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndex.lean#L23-L32
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndex.lean#L23-L32

import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_CommonIndex
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.commonIndexCandidates_isLeast {c : ℝ} (hc : 4 < c) :
    IsLeast (commonIndexCandidates c) 4 := by sorry
