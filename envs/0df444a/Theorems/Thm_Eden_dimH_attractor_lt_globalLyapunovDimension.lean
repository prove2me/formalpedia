-- Prove2me | Theorems.Thm_Eden_dimH_attractor_lt_globalLyapunovDimension
-- name    : Eden.dimH_attractor_lt_globalLyapunovDimension
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:53:29.784513+00:00
-- url     : https://prove2.me/theorems/d8a858a2-f555-4672-826b-626a773ec583
-- title:
--   Eden: dim H attractor lt global Lyapunov Dimension
-- statement:
--   The geometric dimension of A is strictly below its global Lyapunov dimension.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean#L81-L85
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean#L81-L85

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_HausdorffDimensions
import Definitions.Def_Eden_TorusDirections
set_option autoImplicit true
noncomputable section
open Set Filter Topology MeasureTheory
open Eden

theorem Eden.dimH_attractor_lt_globalLyapunovDimension {c : ℝ} (hc : 4 < c) :
    (dimH attractor).toReal < globalLyapunovDimension c attractor := by sorry
