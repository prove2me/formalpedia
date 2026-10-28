-- Prove2me | Theorems.Thm_D1Bound5_smallPair_classified_rectangular
-- name    : D1Bound5.smallPair_classified_rectangular
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:28.239045+00:00
-- url     : https://prove2.me/theorems/8ccd39e4-f639-434f-8787-06fc3b6ced57
-- title:
--   Small Pair classified rectangular
-- statement:
--   Auxiliary result `smallPair_classified_rectangular` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairClassificationData.lean, lines 562-586, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SmallPairClassificationCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairClassificationData_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000















































































































































theorem _root_.D1Bound5.smallPair_classified_rectangular {tau nu : ℤ}
    (htau : tau = 0 ∨ tau = 1) (hlo : 1 ≤ nu) (hhi : nu ≤ 8)
    (a b : QuadInt tau nu) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hroot : ∃ r, r*r = a*b+1) (hnondeg : a*b+1 ≠ 0)
    (hNa : a.norm ≤ 8) (hNb : b.norm ≤ 8) :
    pairCoordinates a b ∈ smallPairTable tau nu := by sorry

end D1Bound5
end
