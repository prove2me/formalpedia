-- Prove2me | Theorems.Thm_Eden_tendstoUniformly_spectrumInterpolation
-- name    : Eden.tendstoUniformly_spectrumInterpolation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:49:01.147164+00:00
-- url     : https://prove2.me/theorems/8fdd4048-6882-5877-b840-cc8ab03e17e6
-- title:
--   Eden: tendsto Uniformly spectrum Interpolation
-- statement:
--   The Eden construction uses the tendsto Uniformly spectrum Interpolation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L108-L116
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L108-L116

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Definitions.Def_Eden_LogarithmicInterpolation
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.tendstoUniformly_spectrumInterpolation {a : ℝ → Fin 5 → ℝ} {b : Fin 5 → ℝ}
    (h : Tendsto a atTop (𝓝 b)) :
    TendstoUniformly (fun t d => spectrumInterpolation (a t) d) (spectrumInterpolation b) atTop := by sorry
