-- Prove2me | Theorems.Thm_D1Bound5_trace_zero_tau_zero_product
-- name    : D1Bound5.trace_zero_tau_zero_product
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:24:02.854126+00:00
-- url     : https://prove2.me/theorems/7a502051-870e-4112-a258-897014b913f5
-- title:
--   Trace zero tau zero product
-- statement:
--   Exact product on the imaginary axis in the trace-zero basis.
-- source:
--   D1Bound5/PairTraceZeroNoThree.lean, lines 29-40, SHA-256 05241394baba13ad0c936d0b25bff457bd0afdadbe4186e3e3cfec5b20a4cbe4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5








theorem _root_.D1Bound5.trace_zero_tau_zero_product {nu : ℤ} (z w : QuadInt 0 nu)
    (hz : 2 * z.re = 0) (hw : 2 * w.re = 0) :
    z * w + 1 = ((1 - nu * z.im * w.im : ℤ) : QuadInt 0 nu) := by sorry















end D1Bound5
end
