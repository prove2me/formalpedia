-- Prove2me | Theorems.Thm_Eden_tendsto_frequencyLyapunovExponent
-- name    : Eden.tendsto_frequencyLyapunovExponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:56:39.283955+00:00
-- url     : https://prove2.me/theorems/9c60c526-9fec-558d-b016-4dcc222e7209
-- title:
--   Eden: tendsto frequency Lyapunov Exponent
-- statement:
--   Ordinary real-time exponent limits for all real parameters and ambient initial points.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L62-L67
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L62-L67

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.tendsto_frequencyLyapunovExponent (c ν : ℝ) (p : PhaseSpace) (i : Fin 5) :
    Tendsto (fun t : ℝ => Real.log
      ((fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) / t)
      atTop (𝓝 (frequencyLyapunovExponent c ν p i)) := by sorry
