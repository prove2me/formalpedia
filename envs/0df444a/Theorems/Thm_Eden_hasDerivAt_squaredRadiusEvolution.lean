-- Prove2me | Theorems.Thm_Eden_hasDerivAt_squaredRadiusEvolution
-- name    : Eden.hasDerivAt_squaredRadiusEvolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:05:44.404225+00:00
-- url     : https://prove2.me/theorems/361df6e6-1edc-532a-b229-7fac25fb2aca
-- title:
--   Eden: has Deriv At squared Radius Evolution
-- statement:
--   The scalar equation holds for every nonnegative time and real initial parameter.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean#L155-L159
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ScalarFlow.lean#L155-L159

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.hasDerivAt_squaredRadiusEvolution {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    HasDerivAt (fun τ => squaredRadiusEvolution τ s)
      (-2 * squaredRadiusEvolution t s * (squaredRadiusEvolution t s - 1) *
        (squaredRadiusEvolution t s - 2)) t := by sorry
