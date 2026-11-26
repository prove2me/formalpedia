-- Prove2me | Theorems.Thm_Eden_spectrumInterpolation_pos_one_two
-- name    : Eden.spectrumInterpolation_pos_one_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:59:32.855964+00:00
-- url     : https://prove2.me/theorems/f35a4504-7046-4b61-9192-cae15c5c07dd
-- title:
--   Eden: spectrum Interpolation pos one two
-- statement:
--   The Eden construction uses the spectrum Interpolation pos one two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LimitingInterpolation.lean#L25-L32
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LimitingInterpolation.lean#L25-L32

import Definitions.Def_Eden_InterpolationSign
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_LimitingInterpolation
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.spectrumInterpolation_pos_one_two {c d : ℝ}
    (hd : d ∈ Ioo 0 (7 / 2)) : 0 < spectrumInterpolation ![2, 0, 0, -4, -c] d := by sorry
