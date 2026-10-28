-- Prove2me | Theorems.Thm_D1Bound5_smallPairTable_1_3_orbits
-- name    : D1Bound5.smallPairTable_1_3_orbits
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:26:58.233988+00:00
-- url     : https://prove2.me/theorems/fa6afdec-77a0-4a78-9201-7d88c82db5f4
-- title:
--   Small Pair Table 1 3 orbits
-- statement:
--   Auxiliary result `smallPairTable_1_3_orbits` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairClassificationData.lean, lines 290-292, SHA-256 0479960d253f413b6231376d75e08d6895df49dd0720f2623e327fcef62f8410. Project: https://github.com/tomislav-math/d1-bound5-lean

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





























































theorem _root_.D1Bound5.smallPairTable_1_3_orbits :
    smallPairs_1_3.toFinset = smallPairRepresentatives_1_3.biUnion (smallTripleOrbit 1) := by sorry



















































































end D1Bound5
end
