-- Prove2me | Theorems.Thm_Eden_hasDerivAt_squaredRadiusEvolution_of_discriminant_pos
-- name    : Eden.hasDerivAt_squaredRadiusEvolution_of_discriminant_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:15.635244+00:00
-- url     : https://prove2.me/theorems/733f580f-b85b-55a7-91cf-82c9c2241ffb
-- title:
--   Eden: has Deriv At squared Radius Evolution of discriminant pos
-- statement:
--   The scalar equation holds locally wherever its discriminant is positive.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean#L133-L152
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean#L133-L152

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.hasDerivAt_squaredRadiusEvolution_of_discriminant_pos {t s : ℝ}
    (hD : 0 < radialDiscriminant t s) :
    HasDerivAt (fun τ => squaredRadiusEvolution τ s)
      (-2 * squaredRadiusEvolution t s * (squaredRadiusEvolution t s - 1) *
        (squaredRadiusEvolution t s - 2)) t := by sorry
