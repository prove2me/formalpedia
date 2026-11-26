-- Prove2me | Theorems.Thm_Eden_spectrumInterpolation_eq_min_sum
-- name    : Eden.spectrumInterpolation_eq_min_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:28:25.088052+00:00
-- url     : https://prove2.me/theorems/2f5de25d-7b69-4589-bf17-855cac196c5e
-- title:
--   Eden: spectrum Interpolation eq min sum
-- statement:
--   A finite summation-by-parts identity on the full dimension interval.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationConcavity.lean#L39-L49
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationConcavity.lean#L39-L49

import Definitions.Def_Eden_LogarithmicInterpolation
import Mathlib.Analysis.Convex.Function
import Definitions.Def_Eden_InterpolationConcavity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.spectrumInterpolation_eq_min_sum (a : Fin 5 → ℝ) {d : ℝ}
    (hd : d ∈ Icc 0 5) :
    spectrumInterpolation a d = a 4 * d +
      (a 0 - a 1) * min d 1 + (a 1 - a 2) * min d 2 +
      (a 2 - a 3) * min d 3 + (a 3 - a 4) * min d 4 := by sorry
