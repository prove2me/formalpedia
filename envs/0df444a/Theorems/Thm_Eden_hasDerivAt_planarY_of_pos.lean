-- Prove2me | Theorems.Thm_Eden_hasDerivAt_planarY_of_pos
-- name    : Eden.hasDerivAt_planarY_of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:03:22.674684+00:00
-- url     : https://prove2.me/theorems/9866f003-9dc9-456b-8792-ca0869eca3e9
-- title:
--   Eden: has Deriv At planar Y of pos
-- statement:
--   The second Cartesian coordinate satisfies the planar vector field.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarFlow.lean#L87-L99
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarFlow.lean#L87-L99

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Eden_PlanarFlow
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.hasDerivAt_planarY_of_pos (Ω : ℝ) {t x y : ℝ}
    (hD : 0 < radialDiscriminant t (x ^ 2 + y ^ 2))
    (hB : 0 < amplitudeSq t (x ^ 2 + y ^ 2)) :
    HasDerivAt (fun τ => planarY Ω τ x y)
      (q (planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2) * planarY Ω t x y +
        Ω * planarX Ω t x y) t := by sorry
