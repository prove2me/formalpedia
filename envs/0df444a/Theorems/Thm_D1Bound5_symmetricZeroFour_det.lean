-- Prove2me | Theorems.Thm_D1Bound5_symmetricZeroFour_det
-- name    : D1Bound5.symmetricZeroFour_det
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:56.123424+00:00
-- url     : https://prove2.me/theorems/88ba7220-5c85-4425-a57d-1a7ae259a190
-- title:
--   Symmetric Zero Four det
-- statement:
--   Exact determinant polynomial of a symmetric zero-diagonal four-by-four matrix.
-- source:
--   D1Bound5/SymmetricFourDetBound.lean, lines 8-18, SHA-256 2a8b9f67b260c4208f344e6df6c355fa9cb7ed11896ad19c480cd1c58d7b2c1c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.symmetricZeroFour_det (x y z u v w : ℂ) :
    ( !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0] :
      Matrix (Fin 4) (Fin 4) ℂ).det =
    (x*w)^2 + (y*v)^2 + (z*u)^2 -
      2 * ((x*w)*(y*v) + (x*w)*(z*u) + (y*v)*(z*u)) := by sorry

end D1Bound5

namespace D1Bound5





end D1Bound5

namespace D1Bound5





end D1Bound5

namespace D1Bound5





end D1Bound5
end
