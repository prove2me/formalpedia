-- Prove2me | Theorems.Thm_Eden_spectrumInterpolation_five
-- name    : Eden.spectrumInterpolation_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:41.787207+00:00
-- url     : https://prove2.me/theorems/4b516350-4d88-57c7-9983-9e4cdeb7dc20
-- title:
--   Eden: spectrum Interpolation five
-- statement:
--   The Eden construction uses the spectrum Interpolation five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L68-L75
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L68-L75

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Definitions.Def_Eden_LogarithmicInterpolation
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.spectrumInterpolation_five (a : Fin 5 → ℝ) :
    spectrumInterpolation a 5 = spectrumPartialSum a 5 := by sorry
