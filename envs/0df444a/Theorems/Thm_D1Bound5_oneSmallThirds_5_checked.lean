-- Prove2me | Theorems.Thm_D1Bound5_oneSmallThirds_5_checked
-- name    : D1Bound5.oneSmallThirds_5_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:42:26.765439+00:00
-- url     : https://prove2.me/theorems/27d89f1d-7611-4ff4-ab86-61b1f44205dc
-- title:
--   One Small Thirds 5 checked
-- statement:
--   Auxiliary result `oneSmallThirds_5_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/OneSmallThirdData.lean, lines 97-100, SHA-256 1a99812615576213a57446af3223d15f39986fed5a03e5b58ab6c3210a77a7c2. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallDisks_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000













































theorem _root_.D1Bound5.oneSmallThirds_5_checked :
    oneSmallThirdCoveredBool oneSmallPairA_5 oneSmallPairB_5
      oneSmallDisk_224_0_1 oneSmallThirds_5 = true := by sorry



















































































































































































































































































end D1Bound5
end
