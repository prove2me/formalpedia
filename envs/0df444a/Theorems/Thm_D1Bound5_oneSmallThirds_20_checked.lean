-- Prove2me | Theorems.Thm_D1Bound5_oneSmallThirds_20_checked
-- name    : D1Bound5.oneSmallThirds_20_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:41:33.074785+00:00
-- url     : https://prove2.me/theorems/9e5a32ad-7017-4c17-b326-28246bac0f68
-- title:
--   One Small Thirds 20 checked
-- statement:
--   Auxiliary result `oneSmallThirds_20_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/OneSmallThirdData.lean, lines 352-355, SHA-256 1a99812615576213a57446af3223d15f39986fed5a03e5b58ab6c3210a77a7c2. Project: https://github.com/tomislav-math/d1-bound5-lean

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





































































































































































theorem _root_.D1Bound5.oneSmallThirds_20_checked :
    oneSmallThirdCoveredBool oneSmallPairA_20 oneSmallPairB_20
      oneSmallDisk_224_1_1 oneSmallThirds_20 = true := by sorry



























































































































































end D1Bound5
end
