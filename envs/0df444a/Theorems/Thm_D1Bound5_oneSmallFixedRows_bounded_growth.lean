-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFixedRows_bounded_growth
-- name    : D1Bound5.oneSmallFixedRows_bounded_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:25:13.265337+00:00
-- url     : https://prove2.me/theorems/b9ae98bb-5798-4574-a545-b60da052f7df
-- title:
--   One Small Fixed Rows bounded growth
-- statement:
--   All 56 bounded complements are checked with exact integral roots. Zero and anchor coincidences are allowed throughout this theorem.
-- source:
--   D1Bound5/OneSmallRows.lean, lines 84-147, SHA-256 5d9e96e3d46ca1e91403fd677ac916a5fa55d59330a9fc532fee6467ec77e849. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5
open QuadInt










theorem _root_.D1Bound5.oneSmallFixedRows_bounded_growth (r : OneSmallTripleRow)
    (hr : r ∈ oneSmallFixedRows) (z : QuadInt r.tau r.nu) (hz : z.norm < r.cutoff)
    (ha : ∃ q, q*q = r.anchorA*z+1) (hb : ∃ q, q*q = r.anchorB*z+1)
    (hs : ∃ q, q*q = r.anchorS*z+1) : z.norm ≤ 4*r.anchorB.norm*r.anchorS.norm := by sorry





















































































end D1Bound5
end
