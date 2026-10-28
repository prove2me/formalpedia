-- Prove2me | Theorems.Thm_D1Bound5_smallTailCheck_rectangular
-- name    : D1Bound5.smallTailCheck_rectangular
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:29:19.437988+00:00
-- url     : https://prove2.me/theorems/b08172ab-7d05-49b7-b639-62da2978834b
-- title:
--   Small Tail Check rectangular
-- statement:
--   Complete finite certificate for the normalized parameter rectangle. Every data equality and every exclusion above is checked by the kernel.
-- source:
--   D1Bound5/SmallTailAllData.lean, lines 485-522, SHA-256 b043adcb34167ee12d7125095cb2fb5aa023d0064768e88ccfe344b7e38716d1. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteTail_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000


































































































































































































































theorem _root_.D1Bound5.smallTailCheck_rectangular (tau nu : ℤ)
    (htau : tau = 0 ∨ tau = 1) (hlo : 1 ≤ nu) (hhi : nu ≤ 15)
    (_hpos : 0 < discriminant tau nu) : SmallTailCheck tau nu := by sorry

end D1Bound5
end
