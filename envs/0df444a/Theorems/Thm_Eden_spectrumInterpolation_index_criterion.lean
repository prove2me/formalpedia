-- Prove2me | Theorems.Thm_Eden_spectrumInterpolation_index_criterion
-- name    : Eden.spectrumInterpolation_index_criterion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:56:57.444376+00:00
-- url     : https://prove2.me/theorems/b0fa0bb3-6736-471f-a5e9-0ec8877d3bf4
-- title:
--   Eden: spectrum Interpolation index criterion
-- statement:
--   The Eden construction uses the spectrum Interpolation index criterion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationSign.lean#L73-L80
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationSign.lean#L73-L80

import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_InterpolationSign
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.spectrumInterpolation_index_criterion {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a < 5) (α : ℝ) :
    0 ≤ spectrumPartialSum a (kaplanYorkeIndex a) + α * spectrumEntry a (kaplanYorkeIndex a) ↔
      (kaplanYorkeIndex a : ℝ) + α ≤ kaplanYorkeDimension a := by sorry
