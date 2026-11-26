-- Prove2me | Theorems.Thm_Eden_norm_fderiv_torus_directions
-- name    : Eden.norm_fderiv_torus_directions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:12:31.337315+00:00
-- url     : https://prove2.me/theorems/3d6e6e17-3ff9-4537-8d01-0f221f3503c1
-- title:
--   Eden: norm fderiv torus directions
-- statement:
--   Exact norms in radial/tangential/radial/tangential/w order, all t≥0.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean#L54-L59
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean#L54-L59

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_HausdorffDimensions
import Definitions.Def_Eden_TorusDirections
set_option autoImplicit true
noncomputable section
open Set Filter Topology MeasureTheory
open Eden

theorem Eden.norm_fderiv_torus_directions (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ torus) (i : Fin 5) :
    ‖fderiv ℝ (evolution c t) p (radialOrthonormalBasis p i)‖ =
      Real.exp ((![2, 0, 2, 0, -c] : Fin 5 → ℝ) i * t) := by sorry
