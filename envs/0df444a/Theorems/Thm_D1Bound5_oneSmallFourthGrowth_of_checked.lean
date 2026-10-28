-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFourthGrowth_of_checked
-- name    : D1Bound5.oneSmallFourthGrowth_of_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:16:18.598983+00:00
-- url     : https://prove2.me/theorems/3e3fd94b-8850-49bf-b2a7-7d4374fc0c3f
-- title:
--   One Small Fourth Growth of checked
-- statement:
--   Auxiliary result `oneSmallFourthGrowth_of_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/OneSmallFiniteCheck.lean, lines 141-157, SHA-256 071c08b2bdc31b423cf7fceaeeb7fd97f8c1844d2c362578eed3d43c62423b55. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions

section
namespace D1Bound5
open QuadInt





















theorem _root_.D1Bound5.oneSmallFourthGrowth_of_checked {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b s : QuadInt tau nu)
    (ha : a ≠ 0) (hNa : a.norm ≤ 2) (cutoff : ℤ) (hcutoff : cutoff ≤ 21270)
    (roots : List (QuadInt tau nu))
    (hcover : ∀ q ∈ disk tau nu 300, q ∈ roots)
    (hcheck : oneSmallFourthGrowthBool a b s cutoff roots = true)
    (z : QuadInt tau nu) (hz : z.norm < cutoff)
    (hza : ∃ q, q*q = a*z+1) (hzb : ∃ q, q*q = b*z+1)
    (hzs : ∃ q, q*q = s*z+1) : z.norm ≤ 4*b.norm*s.norm := by sorry

end D1Bound5
end
