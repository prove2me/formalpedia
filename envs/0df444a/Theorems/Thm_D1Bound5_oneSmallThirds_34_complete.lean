-- Prove2me | Theorems.Thm_D1Bound5_oneSmallThirds_34_complete
-- name    : D1Bound5.oneSmallThirds_34_complete
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:37.578998+00:00
-- url     : https://prove2.me/theorems/c05ca50e-acd5-4e6a-b292-a5b4119680e0
-- title:
--   One Small Thirds 34 complete
-- statement:
--   Auxiliary result `oneSmallThirds_34_complete` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/OneSmallThirdData.lean, lines 595-601, SHA-256 1a99812615576213a57446af3223d15f39986fed5a03e5b58ab6c3210a77a7c2. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallThirdData_Definitions_002
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000























































































































































































































































































theorem _root_.D1Bound5.oneSmallThirds_34_complete (s : QuadInt 1 4) (hbound : s.norm ≤ 224)
    (horder : oneSmallPairB_34.norm ≤ s.norm)
    (ha : s ≠ oneSmallPairA_34) (hb : s ≠ oneSmallPairB_34)
    (hpair : PairExtension oneSmallPairA_34 oneSmallPairB_34 s) : s ∈ oneSmallThirds_34 := by sorry









































end D1Bound5
end
