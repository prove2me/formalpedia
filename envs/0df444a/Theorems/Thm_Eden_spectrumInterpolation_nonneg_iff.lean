-- Prove2me | Theorems.Thm_Eden_spectrumInterpolation_nonneg_iff
-- name    : Eden.spectrumInterpolation_nonneg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:51:48.164092+00:00
-- url     : https://prove2.me/theorems/cbd0cf55-bca5-5f7f-8851-37d7d39451f8
-- title:
--   Eden: spectrum Interpolation nonneg iff
-- statement:
--   For a descending spectrum and every dimension in `[0,5]`, the interpolant
--   is nonnegative exactly at or below the Kaplan--Yorke dimension. Zero partial
--   sums and both ambient endpoints are included.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationSign.lean#L98-L125
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationSign.lean#L98-L125

import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_InterpolationSign
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.spectrumInterpolation_nonneg_iff {a : Fin 5 → ℝ} (ha : Antitone a)
    {d : ℝ} (hd : d ∈ Icc 0 5) :
    0 ≤ spectrumInterpolation a d ↔ d ≤ kaplanYorkeDimension a := by sorry
