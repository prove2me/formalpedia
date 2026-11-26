-- Prove2me | Theorems.Thm_Eden_spectrumInterpolation_neg_iff
-- name    : Eden.spectrumInterpolation_neg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:56:51.584803+00:00
-- url     : https://prove2.me/theorems/332453ab-141f-50c7-8c7c-2e55871384cb
-- title:
--   Eden: spectrum Interpolation neg iff
-- statement:
--   The Eden construction uses the spectrum Interpolation neg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationSign.lean#L127-L130
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationSign.lean#L127-L130

import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_InterpolationSign
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.spectrumInterpolation_neg_iff {a : Fin 5 → ℝ} (ha : Antitone a)
    {d : ℝ} (hd : d ∈ Icc 0 5) :
    spectrumInterpolation a d < 0 ↔ kaplanYorkeDimension a < d := by sorry
