-- Prove2me | Theorems.Thm_Eden_commonIndexLocalDimension_eq
-- name    : Eden.commonIndexLocalDimension_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:04:39.402006+00:00
-- url     : https://prove2.me/theorems/9e11a55d-d4e4-58dd-99f2-a97667b42329
-- title:
--   Eden: common Index Local Dimension eq
-- statement:
--   The Eden construction uses the common Index Local Dimension eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndex.lean#L54-L56
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CommonIndex.lean#L54-L56

import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_CommonIndex
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.commonIndexLocalDimension_eq {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    commonIndexLocalDimension c p = 4 + spectrumPartialSum (lyapunovExponent c p) 4 / c := by sorry
