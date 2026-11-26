-- Prove2me | Theorems.Thm_Eden_tendstoUniformlyOn_log_singularValueFunction
-- name    : Eden.tendstoUniformlyOn_log_singularValueFunction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:09:46.415736+00:00
-- url     : https://prove2.me/theorems/befd44fb-09b4-53dc-bc0a-802d1a467b47
-- title:
--   Eden: tendsto Uniformly On log singular Value Function
-- statement:
--   Uniform real-time convergence on the complete dimension interval.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L119-L131
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicInterpolation.lean#L119-L131

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Definitions.Def_Eden_LogarithmicInterpolation
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.tendstoUniformlyOn_log_singularValueFunction (c : ℝ) (p : PhaseSpace) :
    TendstoUniformlyOn (fun t d => Real.log
      (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t)
      (spectrumInterpolation (lyapunovExponent c p)) atTop (Icc 0 5) := by sorry
