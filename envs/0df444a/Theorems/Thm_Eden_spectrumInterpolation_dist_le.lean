-- Prove2me | Theorems.Thm_Eden_spectrumInterpolation_dist_le
-- name    : Eden.spectrumInterpolation_dist_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:49:12.099511+00:00
-- url     : https://prove2.me/theorems/04d6b59e-ebe8-43d6-b745-c16ab4e23b8e
-- title:
--   Eden: spectrum Interpolation dist le
-- statement:
--   A bound uniform in dimension, including both endpoints.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L78-L93
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L78-L93

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Definitions.Def_Eden_LogarithmicInterpolation
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.spectrumInterpolation_dist_le (a b : Fin 5 → ℝ) (d : ℝ) :
    dist (spectrumInterpolation a d) (spectrumInterpolation b d) ≤ 5 * dist a b := by sorry
