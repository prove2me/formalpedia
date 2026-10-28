-- Prove2me | Theorems.Thm_D1Bound5_eisenstein_trace_zero_compatible_opposite
-- name    : D1Bound5.eisenstein_trace_zero_compatible_opposite
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:07:27.779756+00:00
-- url     : https://prove2.me/theorems/cc5bf421-b03f-462a-9cf7-7cdd7a7792ba
-- title:
--   Eisenstein trace zero compatible opposite
-- statement:
--   Two compatible nonzero purely imaginary Eisenstein integers must lie on opposite half-axes. The zero-root case is included in the input.
-- source:
--   D1Bound5/EisensteinImaginaryExtensions.lean, lines 31-50, SHA-256 1a43096b0a3b24a44183306c5af3c14190bbed00150a819de4741684b454e355. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5






theorem _root_.D1Bound5.eisenstein_trace_zero_compatible_opposite
    (z w : QuadInt 1 1) (hz0 : z ≠ 0) (hw0 : w ≠ 0)
    (hz : 2 * z.re + z.im = 0) (hw : 2 * w.re + w.im = 0)
    (hsquare : ∃ r : QuadInt 1 1, r * r = z * w + 1) :
    z.re * w.re < 0 := by sorry





end D1Bound5
end
