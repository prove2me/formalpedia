-- Prove2me | Theorems.Thm_Eden_concaveOn_log_singularValueFunction
-- name    : Eden.concaveOn_log_singularValueFunction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:05:45.891329+00:00
-- url     : https://prove2.me/theorems/26f04c94-a0e5-4bf7-8b49-918c0b628864
-- title:
--   Eden: concave On log singular Value Function
-- statement:
--   Concavity of the finite-time logarithmic singular-value function.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationConcavity.lean#L81-L88
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationConcavity.lean#L81-L88

import Definitions.Def_Eden_LogarithmicInterpolation
import Mathlib.Analysis.Convex.Function
import Definitions.Def_Eden_InterpolationConcavity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.concaveOn_log_singularValueFunction (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) :
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (fun d => Real.log
      (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t) := by sorry
