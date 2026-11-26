-- Prove2me | Theorems.Thm_Eden_tendsto_torus_direction_growth
-- name    : Eden.tendsto_torus_direction_growth
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:53:41.216875+00:00
-- url     : https://prove2.me/theorems/3d1b5da0-a091-457c-9d52-74f078d5ae80
-- title:
--   Eden: tendsto torus direction growth
-- statement:
--   Each displayed direction has its stated ordinary real-time growth limit.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean#L62-L70
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean#L62-L70

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_HausdorffDimensions
import Definitions.Def_Eden_TorusDirections
set_option autoImplicit true
noncomputable section
open Set Filter Topology MeasureTheory
open Eden

theorem Eden.tendsto_torus_direction_growth (c : ℝ) {p : PhaseSpace} (hp : p ∈ torus)
    (i : Fin 5) :
    Tendsto (fun t : ℝ => Real.log
      ‖fderiv ℝ (evolution c t) p (radialOrthonormalBasis p i)‖ / t)
      atTop (𝓝 ((![2, 0, 2, 0, -c] : Fin 5 → ℝ) i)) := by sorry
