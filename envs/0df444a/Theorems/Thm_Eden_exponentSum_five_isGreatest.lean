-- Prove2me | Theorems.Thm_Eden_exponentSum_five_isGreatest
-- name    : Eden.exponentSum_five_isGreatest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:05.261258+00:00
-- url     : https://prove2.me/theorems/96086417-c86a-5260-bc8a-f3ba2fe00bb4
-- title:
--   Eden: exponent Sum five is Greatest
-- statement:
--   The Eden construction uses the exponent Sum five is Greatest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L113-L122
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L113-L122

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exponentSum_five_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest ((fun p => spectrumPartialSum (lyapunovExponent c p) 5) '' attractor)
      (4 - c) := by sorry
