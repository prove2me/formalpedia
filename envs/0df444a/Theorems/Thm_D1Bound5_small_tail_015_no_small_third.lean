-- Prove2me | Theorems.Thm_D1Bound5_small_tail_015_no_small_third
-- name    : D1Bound5.small_tail_015_no_small_third
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:16:15.592958+00:00
-- url     : https://prove2.me/theorems/d25bbeb7-d003-41b8-b779-24c6ef9a4c1d
-- title:
--   Small tail 015 no small third
-- statement:
--   Neither opposite imaginary pair has a compatible nonzero third entry of norm at most fifteen.
-- source:
--   D1Bound5/SmallTailModel15.lean, lines 19-25, SHA-256 e96aba3f8c1850d6941f20a160242cec6807927449cf2c5c5d3969a2ac4fd551. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions

section
namespace D1Bound5
open QuadInt

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000




theorem _root_.D1Bound5.small_tail_015_no_small_third :
    ∀ a ∈ disk 0 15 15, a ≠ 0 →
      hasSquareRoot (a*(⟨0,-1⟩ : QuadInt 0 15)+1) = false ∨
      hasSquareRoot (a*(⟨0,1⟩ : QuadInt 0 15)+1) = false := by sorry



end D1Bound5
end
