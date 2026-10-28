-- Prove2me | Theorems.Thm_D1Bound5_eisenstein_trace_zero_product
-- name    : D1Bound5.eisenstein_trace_zero_product
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:08:09.863013+00:00
-- url     : https://prove2.me/theorems/e4c614ac-896a-406a-a93e-36ef4edba7ad
-- title:
--   Eisenstein trace zero product
-- statement:
--   The product of two purely imaginary Eisenstein integers is the ordinary integer -3 times the product of their real coordinates.
-- source:
--   D1Bound5/EisensteinImaginaryExtensions.lean, lines 17-29, SHA-256 1a43096b0a3b24a44183306c5af3c14190bbed00150a819de4741684b454e355. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.eisenstein_trace_zero_product (z w : QuadInt 1 1)
    (hz : 2 * z.re + z.im = 0) (hw : 2 * w.re + w.im = 0) :
    z * w + 1 = ((1 - 3 * z.re * w.re : ℤ) : QuadInt 1 1) := by sorry







end D1Bound5
end
