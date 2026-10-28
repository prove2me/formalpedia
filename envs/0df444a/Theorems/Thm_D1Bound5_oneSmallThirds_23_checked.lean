-- Prove2me | Theorems.Thm_D1Bound5_oneSmallThirds_23_checked
-- name    : D1Bound5.oneSmallThirds_23_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:41:33.635907+00:00
-- url     : https://prove2.me/theorems/a9a57dae-821f-4b6b-aa31-a818955e3d30
-- title:
--   One Small Thirds 23 checked
-- statement:
--   Auxiliary result `oneSmallThirds_23_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/OneSmallThirdData.lean, lines 403-406, SHA-256 1a99812615576213a57446af3223d15f39986fed5a03e5b58ab6c3210a77a7c2. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000





























































































































































































theorem _root_.D1Bound5.oneSmallThirds_23_checked :
    oneSmallThirdCoveredBool oneSmallPairA_23 oneSmallPairB_23
      oneSmallDisk_224_1_1 oneSmallThirds_23 = true := by sorry



































































































































end D1Bound5
end
