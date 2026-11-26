-- Prove2me | Theorems.Thm_Eden_tendsto_finiteTimeDimension
-- name    : Eden.tendsto_finiteTimeDimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:11:24.020811+00:00
-- url     : https://prove2.me/theorems/617343c0-355e-49e3-8830-5a3372368b7c
-- title:
--   Eden: tendsto finite Time Dimension
-- statement:
--   The pointwise dimension limit, including every boundary radius
--   and both neutral rows of the limiting spectrum table.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionConvergence.lean#L62-L109
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionConvergence.lean#L62-L109

import Definitions.Def_Eden_DimensionConvergenceCriteria
import Definitions.Def_Eden_NeutralDimensionBounds
import Definitions.Def_Eden_LimitingInterpolation
import Definitions.Def_Eden_DimensionConvergence
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.tendsto_finiteTimeDimension {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by sorry
