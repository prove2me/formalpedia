-- Prove2me | Theorems.Thm_Eden_log_singularValueFunction_div_time
-- name    : Eden.log_singularValueFunction_div_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:48:55.527574+00:00
-- url     : https://prove2.me/theorems/84d40239-d227-5523-b6dc-b40aab08c20c
-- title:
--   Eden: log singular Value Function div time
-- statement:
--   The Eden construction uses the log singular Value Function div time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L95-L106
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L95-L106

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Definitions.Def_Eden_LogarithmicInterpolation
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.log_singularValueFunction_div_time (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) (d : ℝ) :
    Real.log (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t =
      spectrumInterpolation (normalizedLogSingularValues c t p) d := by sorry
