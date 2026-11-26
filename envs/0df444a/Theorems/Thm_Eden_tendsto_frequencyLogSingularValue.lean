-- Prove2me | Theorems.Thm_Eden_tendsto_frequencyLogSingularValue
-- name    : Eden.tendsto_frequencyLogSingularValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:21:30.847547+00:00
-- url     : https://prove2.me/theorems/0fe6502d-0269-4120-aca8-a4dd6d4acd9c
-- title:
--   Eden: tendsto frequency Log Singular Value
-- statement:
--   The Eden construction uses the tendsto frequency Log Singular Value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L49-L55
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L49-L55

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.tendsto_frequencyLogSingularValue (c ν : ℝ) (p : PhaseSpace) (i : Fin 5) :
    Tendsto (fun t : ℝ => Real.log
      ((fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) / t)
      atTop (𝓝 (lyapunovExponent c p i)) := by sorry
