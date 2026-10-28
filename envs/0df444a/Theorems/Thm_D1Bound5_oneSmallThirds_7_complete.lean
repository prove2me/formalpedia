-- Prove2me | Theorems.Thm_D1Bound5_oneSmallThirds_7_complete
-- name    : D1Bound5.oneSmallThirds_7_complete
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:19:37.528237+00:00
-- url     : https://prove2.me/theorems/2814f3ae-b724-4f22-b793-8fc507bddf36
-- title:
--   One Small Thirds 7 complete
-- statement:
--   Auxiliary result `oneSmallThirds_7_complete` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/OneSmallThirdData.lean, lines 136-142, SHA-256 1a99812615576213a57446af3223d15f39986fed5a03e5b58ab6c3210a77a7c2. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_001
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000































































theorem _root_.D1Bound5.oneSmallThirds_7_complete (s : QuadInt 0 2) (hbound : s.norm ≤ 224)
    (horder : oneSmallPairB_7.norm ≤ s.norm)
    (ha : s ≠ oneSmallPairA_7) (hb : s ≠ oneSmallPairB_7)
    (hpair : PairExtension oneSmallPairA_7 oneSmallPairB_7 s) : s ∈ oneSmallThirds_7 := by sorry

































































































































































































































































end D1Bound5
end
