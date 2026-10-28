-- Prove2me | Theorems.Thm_D1Bound5_oneSmallThirdCovered_of_checked
-- name    : D1Bound5.oneSmallThirdCovered_of_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:45:03.898554+00:00
-- url     : https://prove2.me/theorems/0de66161-de61-446d-9e82-88033c1fc204
-- title:
--   One Small Third Covered of checked
-- statement:
--   Auxiliary result `oneSmallThirdCovered_of_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/OneSmallFiniteCheck.lean, lines 117-128, SHA-256 071c08b2bdc31b423cf7fceaeeb7fd97f8c1844d2c362578eed3d43c62423b55. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions

section
namespace D1Bound5
open QuadInt

















theorem _root_.D1Bound5.oneSmallThirdCovered_of_checked {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b : QuadInt tau nu)
    (diskEntries allowed : List (QuadInt tau nu))
    (hcover : ∀ s ∈ disk tau nu 224, s ∈ diskEntries)
    (hcheck : oneSmallThirdCoveredBool a b diskEntries allowed = true)
    (s : QuadInt tau nu) (hbound : s.norm ≤ 224) (horder : b.norm ≤ s.norm)
    (ha : s ≠ a) (hb : s ≠ b) (hpair : PairExtension a b s) : s ∈ allowed := by sorry





end D1Bound5
end
