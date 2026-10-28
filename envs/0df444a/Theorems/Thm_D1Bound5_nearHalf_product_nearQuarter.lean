-- Prove2me | Theorems.Thm_D1Bound5_nearHalf_product_nearQuarter
-- name    : D1Bound5.nearHalf_product_nearQuarter
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:28:15.842615+00:00
-- url     : https://prove2.me/theorems/a92820cf-3762-4484-b5b1-93c14e309842
-- title:
--   Near Half product near Quarter
-- statement:
--   Products of two entries near one half are near one quarter.
-- source:
--   D1Bound5/SymmetricFourDetBound.lean, lines 24-59, SHA-256 2a8b9f67b260c4208f344e6df6c355fa9cb7ed11896ad19c480cd1c58d7b2c1c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open Matrix

namespace D1Bound5



end D1Bound5

namespace D1Bound5


theorem _root_.D1Bound5.nearHalf_product_nearQuarter (x y : ℂ)
    (hx : ‖x - (1/2 : ℂ)‖ < (128/8649 : ℝ))
    (hy : ‖y - (1/2 : ℂ)‖ < (128/8649 : ℝ)) :
    ‖x*y - (1/4 : ℂ)‖ < (1/40 : ℝ) := by sorry



end D1Bound5

namespace D1Bound5





end D1Bound5

namespace D1Bound5





end D1Bound5
end
