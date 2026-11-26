-- Prove2me | Theorems.Thm_Eden_torus_direction_rates_and_ordered_exponents
-- name    : Eden.torus_direction_rates_and_ordered_exponents
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:53:43.678381+00:00
-- url     : https://prove2.me/theorems/14f52704-9ee5-4e94-9e97-3cd6835cbdd5
-- title:
--   Eden: torus direction rates and ordered exponents
-- statement:
--   The sorted ambient exponents are (2,2,0,0,-c), with positive expansion rate two
--   and negative contracting rate -c for c>4.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean#L74-L78
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean#L74-L78

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_HausdorffDimensions
import Definitions.Def_Eden_TorusDirections
set_option autoImplicit true
noncomputable section
open Set Filter Topology MeasureTheory
open Eden

theorem Eden.torus_direction_rates_and_ordered_exponents {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ torus) :
    lyapunovExponent c p = ![2, 2, 0, 0, -c] ∧
      0 < (2 : ℝ) ∧ -c < 0 := by sorry
