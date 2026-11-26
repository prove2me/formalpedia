-- Prove2me | Theorems.Thm_Eden_commonIndexRatio_eq
-- name    : Eden.commonIndexRatio_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:04:28.184856+00:00
-- url     : https://prove2.me/theorems/e51522d1-31af-4c01-b4a4-4d7d52099bf5
-- title:
--   Eden: common Index Ratio eq
-- statement:
--   The Eden construction uses the common Index Ratio eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndex.lean#L50-L52
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndex.lean#L50-L52

import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_CommonIndex
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.commonIndexRatio_eq {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    commonIndexRatio c p = spectrumPartialSum (lyapunovExponent c p) 4 / c := by sorry
