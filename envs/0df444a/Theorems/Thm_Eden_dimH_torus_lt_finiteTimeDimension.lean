-- Prove2me | Theorems.Thm_Eden_dimH_torus_lt_finiteTimeDimension
-- name    : Eden.dimH_torus_lt_finiteTimeDimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:53:34.21215+00:00
-- url     : https://prove2.me/theorems/80df71dd-b104-558e-884f-5e73398f5640
-- title:
--   Eden: dim H torus lt finite Time Dimension
-- statement:
--   The geometric torus dimension is strictly below the finite-time dimension there.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean#L88-L95
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean#L88-L95

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_HausdorffDimensions
import Definitions.Def_Eden_TorusDirections
set_option autoImplicit true
noncomputable section
open Set Filter Topology MeasureTheory
open Eden

theorem Eden.dimH_torus_lt_finiteTimeDimension {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ torus) :
    (dimH torus).toReal < finiteTimeDimension c t p := by sorry
