-- Prove2me | Theorems.Thm_Eden_concaveOn_spectrumInterpolation
-- name    : Eden.concaveOn_spectrumInterpolation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:28:24.151614+00:00
-- url     : https://prove2.me/theorems/82a1d4dc-6bc7-4190-8fdc-8550c6f5c0bf
-- title:
--   Eden: concave On spectrum Interpolation
-- statement:
--   Concavity includes both endpoints and allows repeated or zero slopes.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationConcavity.lean#L64-L78
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationConcavity.lean#L64-L78

import Definitions.Def_Eden_LogarithmicInterpolation
import Mathlib.Analysis.Convex.Function
import Definitions.Def_Eden_InterpolationConcavity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.concaveOn_spectrumInterpolation {a : Fin 5 → ℝ} (ha : Antitone a) :
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (spectrumInterpolation a) := by sorry
