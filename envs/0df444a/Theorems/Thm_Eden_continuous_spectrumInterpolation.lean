-- Prove2me | Theorems.Thm_Eden_continuous_spectrumInterpolation
-- name    : Eden.continuous_spectrumInterpolation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:09:46.459723+00:00
-- url     : https://prove2.me/theorems/0a3d36f7-fcf3-42c8-82e8-62c550e80fbb
-- title:
--   Eden: continuous spectrum Interpolation
-- statement:
--   The Eden construction uses the continuous spectrum Interpolation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L31-L34
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L31-L34

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Definitions.Def_Eden_LogarithmicInterpolation
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.continuous_spectrumInterpolation (a : Fin 5 → ℝ) :
    Continuous (spectrumInterpolation a) := by sorry
