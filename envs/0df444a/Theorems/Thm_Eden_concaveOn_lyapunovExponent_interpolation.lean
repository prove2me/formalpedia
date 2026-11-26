-- Prove2me | Theorems.Thm_Eden_concaveOn_lyapunovExponent_interpolation
-- name    : Eden.concaveOn_lyapunovExponent_interpolation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:05:48.37728+00:00
-- url     : https://prove2.me/theorems/7c7d3a43-0e6e-4dbb-86f1-27d813b02fd5
-- title:
--   Eden: concave On lyapunov Exponent interpolation
-- statement:
--   Concavity of the partial-sum interpolant of the limiting exponents.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationConcavity.lean#L91-L93
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InterpolationConcavity.lean#L91-L93

import Definitions.Def_Eden_LogarithmicInterpolation
import Mathlib.Analysis.Convex.Function
import Definitions.Def_Eden_InterpolationConcavity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.concaveOn_lyapunovExponent_interpolation (c : ℝ) (p : PhaseSpace) :
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (spectrumInterpolation (lyapunovExponent c p)) := by sorry
