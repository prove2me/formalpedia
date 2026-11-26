-- Prove2me | Theorems.Thm_Eden_planar_radius_sq_of_pos
-- name    : Eden.planar_radius_sq_of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:32.995911+00:00
-- url     : https://prove2.me/theorems/a9d232d3-b381-5370-95f9-d99c112f5f8c
-- title:
--   Eden: planar radius sq of pos
-- statement:
--   The Cartesian solution has the squared radius given by the scalar equation.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarFlow.lean#L41-L56
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarFlow.lean#L41-L56

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Eden_PlanarFlow
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.planar_radius_sq_of_pos (Ω : ℝ) {t x y : ℝ}
    (hD : 0 < radialDiscriminant t (x ^ 2 + y ^ 2))
    (hB : 0 < amplitudeSq t (x ^ 2 + y ^ 2)) :
    planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2 =
      squaredRadiusEvolution t (x ^ 2 + y ^ 2) := by sorry
