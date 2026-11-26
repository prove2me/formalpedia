-- Prove2me | Theorems.Thm_Eden_frequencyGlobalLyapunovDimension_attractor
-- name    : Eden.frequencyGlobalLyapunovDimension_attractor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:57:17.754244+00:00
-- url     : https://prove2.me/theorems/12a56df8-955a-4c97-886f-50ab422961d3
-- title:
--   Eden: frequency Global Lyapunov Dimension attractor
-- statement:
--   The positive-time infimum of the spatial suprema on A equals 4 + 4/c.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L118-L120
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyDimensions.lean#L118-L120

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.frequencyGlobalLyapunovDimension_attractor {c : ℝ} (hc : 4 < c) (ν : ℝ) :
    frequencyGlobalLyapunovDimension c ν attractor = 4 + 4 / c := by sorry
