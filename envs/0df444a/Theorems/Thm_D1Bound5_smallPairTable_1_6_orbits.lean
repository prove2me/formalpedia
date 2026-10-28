-- Prove2me | Theorems.Thm_D1Bound5_smallPairTable_1_6_orbits
-- name    : D1Bound5.smallPairTable_1_6_orbits
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:22:34.867907+00:00
-- url     : https://prove2.me/theorems/d4f8d6ea-785d-4cd1-aa02-356836097f0e
-- title:
--   Small Pair Table 1 6 orbits
-- statement:
--   Auxiliary result `smallPairTable_1_6_orbits` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairClassificationData.lean, lines 311-313, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairClassificationData_Definitions
import Definitions.Def_D1Bound5_SmallTripleData_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000









































































theorem _root_.D1Bound5.smallPairTable_1_6_orbits :
    smallPairs_1_6.toFinset = smallPairRepresentatives_1_6.biUnion (smallTripleOrbit 1) := by sorry







































































end D1Bound5
end
