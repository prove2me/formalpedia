-- Prove2me | Theorems.Thm_Eden_spectrumInterpolation_pos_one_one
-- name    : Eden.spectrumInterpolation_pos_one_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:59:08.702212+00:00
-- url     : https://prove2.me/theorems/5e71b726-0aba-5fd8-bd4f-ba9b77511bf0
-- title:
--   Eden: spectrum Interpolation pos one one
-- statement:
--   The Eden construction uses the spectrum Interpolation pos one one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LimitingInterpolation.lean#L34-L46
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LimitingInterpolation.lean#L34-L46

import Definitions.Def_Eden_InterpolationSign
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_LimitingInterpolation
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.spectrumInterpolation_pos_one_one {c d : ℝ} (hc : 4 < c)
    (hd : d ∈ Ioo 0 (targetDimension c)) :
    0 < spectrumInterpolation ![2, 2, 0, 0, -c] d := by sorry
