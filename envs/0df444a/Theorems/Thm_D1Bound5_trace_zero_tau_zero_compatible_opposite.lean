-- Prove2me | Theorems.Thm_D1Bound5_trace_zero_tau_zero_compatible_opposite
-- name    : D1Bound5.trace_zero_tau_zero_compatible_opposite
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:20:09.655355+00:00
-- url     : https://prove2.me/theorems/b905bfde-8bbb-4271-b51e-220035aae038
-- title:
--   Trace zero tau zero compatible opposite
-- statement:
--   Two compatible nonzero imaginary-axis elements have opposite signs. The assumption nu>1 excludes the Gaussian case.
-- source:
--   D1Bound5/PairTraceZeroNoThree.lean, lines 42-61, SHA-256 05241394baba13ad0c936d0b25bff457bd0afdadbe4186e3e3cfec5b20a4cbe4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5










theorem _root_.D1Bound5.trace_zero_tau_zero_compatible_opposite {nu : ℤ} (hnu : 1 < nu)
    (z w : QuadInt 0 nu) (hz0 : z ≠ 0) (hw0 : w ≠ 0)
    (hz : 2 * z.re = 0) (hw : 2 * w.re = 0)
    (hsquare : ∃ r : QuadInt 0 nu, r * r = z * w + 1) :
    z.im * w.im < 0 := by sorry













end D1Bound5
end
