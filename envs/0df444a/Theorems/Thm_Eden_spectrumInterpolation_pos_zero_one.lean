-- Prove2me | Theorems.Thm_Eden_spectrumInterpolation_pos_zero_one
-- name    : Eden.spectrumInterpolation_pos_zero_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:58:58.789157+00:00
-- url     : https://prove2.me/theorems/ce356830-d081-5be5-9715-3121ab7260da
-- title:
--   Eden: spectrum Interpolation pos zero one
-- statement:
--   The Eden construction uses the spectrum Interpolation pos zero one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LimitingInterpolation.lean#L16-L23
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LimitingInterpolation.lean#L16-L23

import Definitions.Def_Eden_InterpolationSign
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_LimitingInterpolation
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.spectrumInterpolation_pos_zero_one {c d : ℝ}
    (hd : d ∈ Ioo 0 3) : 0 < spectrumInterpolation ![2, 0, -2, -2, -c] d := by sorry
