-- Prove2me | Theorems.Thm_Eden_hasDerivAt_planarX_of_pos
-- name    : Eden.hasDerivAt_planarX_of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:56.853099+00:00
-- url     : https://prove2.me/theorems/a3df6b80-ff0f-5ae3-9fac-9b56f1981b52
-- title:
--   Eden: has Deriv At planar X of pos
-- statement:
--   The first Cartesian coordinate satisfies the planar vector field.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarFlow.lean#L65-L77
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarFlow.lean#L65-L77

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Eden_PlanarFlow
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.hasDerivAt_planarX_of_pos (Ω : ℝ) {t x y : ℝ}
    (hD : 0 < radialDiscriminant t (x ^ 2 + y ^ 2))
    (hB : 0 < amplitudeSq t (x ^ 2 + y ^ 2)) :
    HasDerivAt (fun τ => planarX Ω τ x y)
      (q (planarX Ω t x y ^ 2 + planarY Ω t x y ^ 2) * planarX Ω t x y -
        Ω * planarY Ω t x y) t := by sorry
