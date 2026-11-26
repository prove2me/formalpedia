-- Prove2me | Theorems.Thm_Eden_tendsto_frequencyFiniteTimeDimension
-- name    : Eden.tendsto_frequencyFiniteTimeDimension
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:56:42.727402+00:00
-- url     : https://prove2.me/theorems/b6d42d2d-2dff-5081-aaea-8d4e14ff3de7
-- title:
--   Eden: tendsto frequency Finite Time Dimension
-- statement:
--   On A, finite-time dimensions converge for every real frequency when c > 4.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L81-L88
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L81-L88

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.tendsto_frequencyFiniteTimeDimension {c : ℝ} (hc : 4 < c) (ν : ℝ)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    Tendsto (fun t : ℝ => frequencyFiniteTimeDimension c ν t p) atTop
      (𝓝 (frequencyAsymptoticDimension c ν p)) := by sorry
