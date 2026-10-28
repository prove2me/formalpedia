-- Prove2me | Theorems.Thm_D1Bound5_QuadInt_rootCandidate_complete
-- name    : D1Bound5.QuadInt.rootCandidate_complete
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:48:52.440988+00:00
-- url     : https://prove2.me/theorems/1114c5d6-c5bb-4c88-87c1-c6bb97974363
-- title:
--   Quad Int — root Candidate complete
-- statement:
--   Completeness of the exact candidate, for every positive-discriminant coordinate ring and arbitrary input size. No nonzero-root assumption occurs.
-- source:
--   D1Bound5/SquareTest.lean, lines 66-106, SHA-256 adcc13a33378056841f44d21785e69909232e4def68eb73ca742e5a49ce15ac3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions

section
namespace D1Bound5.QuadInt

variable {tau nu : ℤ}












theorem _root_.D1Bound5.QuadInt.rootCandidate_complete (hd : 0 < discriminant tau nu)
    {z : QuadInt tau nu} (hz : ∃ r, r*r = z) : rootCandidate z*rootCandidate z = z := by sorry













end D1Bound5.QuadInt
end
