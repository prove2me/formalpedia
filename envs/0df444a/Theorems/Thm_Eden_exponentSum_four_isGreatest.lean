-- Prove2me | Theorems.Thm_Eden_exponentSum_four_isGreatest
-- name    : Eden.exponentSum_four_isGreatest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:02:32.37512+00:00
-- url     : https://prove2.me/theorems/94bde3db-2c98-5f7d-b930-6ee51988e4f1
-- title:
--   Eden: exponent Sum four is Greatest
-- statement:
--   The Eden construction uses the exponent Sum four is Greatest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L104-L111
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L104-L111

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exponentSum_four_isGreatest {c : ℝ} (hc : 4 < c) :
    IsGreatest ((fun p => spectrumPartialSum (lyapunovExponent c p) 4) '' attractor) 4 := by sorry
