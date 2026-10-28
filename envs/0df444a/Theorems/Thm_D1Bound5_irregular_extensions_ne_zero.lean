-- Prove2me | Theorems.Thm_D1Bound5_irregular_extensions_ne_zero
-- name    : D1Bound5.irregular_extensions_ne_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:44:05.797004+00:00
-- url     : https://prove2.me/theorems/05e12940-c4dc-47c1-893b-8090808e175e
-- title:
--   Irregular extensions ne zero
-- statement:
--   Irregularity makes both algebraic extensions nonzero.
-- source:
--   D1Bound5/Regular.lean, lines 31-45, SHA-256 216649d224d94c38aed36aa23129fd314ab8957413daa9e4aa3f53dd8156c10a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Regular_Definitions

section
namespace D1Bound5










theorem _root_.D1Bound5.irregular_extensions_ne_zero {R : Type*} [CommRing R]
    (a b c r s t : R) (hr : r^2 = a*b+1) (hs : s^2 = a*c+1)
    (ht : t^2 = b*c+1) (hi : regularDefect a b c ≠ 0) :
    a+b+c+2*a*b*c+2*r*s*t ≠ 0 ∧ a+b+c+2*a*b*c-2*r*s*t ≠ 0 := by sorry

end D1Bound5
end
