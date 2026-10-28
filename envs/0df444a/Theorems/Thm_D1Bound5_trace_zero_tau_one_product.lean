-- Prove2me | Theorems.Thm_D1Bound5_trace_zero_tau_one_product
-- name    : D1Bound5.trace_zero_tau_one_product
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:45.439391+00:00
-- url     : https://prove2.me/theorems/068ab002-3725-4996-b081-6a44576e2ccc
-- title:
--   Trace zero tau one product
-- statement:
--   Exact product on the imaginary axis in the trace-one basis.
-- source:
--   D1Bound5/PairTraceZeroNoThree.lean, lines 89-100, SHA-256 05241394baba13ad0c936d0b25bff457bd0afdadbe4186e3e3cfec5b20a4cbe4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
















theorem _root_.D1Bound5.trace_zero_tau_one_product {nu : ℤ} (z w : QuadInt 1 nu)
    (hz : 2 * z.re + z.im = 0) (hw : 2 * w.re + w.im = 0) :
    z * w + 1 = ((1 - (4 * nu - 1) * z.re * w.re : ℤ) : QuadInt 1 nu) := by sorry







end D1Bound5
end
