-- Prove2me | Theorems.Thm_Eden_spectrumInterpolation_zero
-- name    : Eden.spectrumInterpolation_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:49:00.679562+00:00
-- url     : https://prove2.me/theorems/57a98f7e-4b97-4d9c-aedd-4b732c685f81
-- title:
--   Eden: spectrum Interpolation zero
-- statement:
--   The Eden construction uses the spectrum Interpolation zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L64-L66
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L64-L66

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Definitions.Def_Eden_LogarithmicInterpolation
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.spectrumInterpolation_zero (a : Fin 5 → ℝ) :
    spectrumInterpolation a 0 = 0 := by sorry
