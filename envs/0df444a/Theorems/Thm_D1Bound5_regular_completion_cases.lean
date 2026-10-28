-- Prove2me | Theorems.Thm_D1Bound5_regular_completion_cases
-- name    : D1Bound5.regular_completion_cases
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:14:24.286449+00:00
-- url     : https://prove2.me/theorems/5b9bd10d-ef3d-4b9b-9f44-1b2199a1ebea
-- title:
--   Regular completion cases
-- statement:
--   Every regular completion is one of the two completions formed from any chosen root of bc+1. Zero roots cause no exception.
-- source:
--   D1Bound5/FiniteTail.lean, lines 21-33, SHA-256 4a84a3e4ca3b7d43920e93e12f04cbea329f4d21bc5572c8337e09d252793110. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_Regular_Definitions

section
namespace D1Bound5

open QuadInt




theorem _root_.D1Bound5.regular_completion_cases {tau nu : ℤ} (hd : 0 < QuadInt.discriminant tau nu)
    (b c d r : QuadInt tau nu) (hr : r*r = b*c+1) (hreg : regularDefect b c d = 0) :
    d = b+c+2*r ∨ d = b+c-2*r := by sorry










end D1Bound5
end
