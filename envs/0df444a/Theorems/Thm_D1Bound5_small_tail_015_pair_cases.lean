-- Prove2me | Theorems.Thm_D1Bound5_small_tail_015_pair_cases
-- name    : D1Bound5.small_tail_015_pair_cases
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:19:19.124168+00:00
-- url     : https://prove2.me/theorems/7108e744-9702-433e-9c32-89c531caeb84
-- title:
--   Small tail 015 pair cases
-- statement:
--   For omega^2 = -15, the large compatible ordered pairs in the closed norm-15 disk are exactly the opposite imaginary elements.
-- source:
--   D1Bound5/SmallTailModel15.lean, lines 9-17, SHA-256 e96aba3f8c1850d6941f20a160242cec6807927449cf2c5c5d3969a2ac4fd551. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.small_tail_015_pair_cases :
    ∀ b ∈ disk 0 15 15, ∀ c ∈ disk 0 15 15,
      9 ≤ b.norm → b.norm ≤ c.norm → b ≠ c →
      hasSquareRoot (b*c+1) = true →
      (b = (⟨0,-1⟩ : QuadInt 0 15) ∧ c = ⟨0,1⟩) ∨
      (b = (⟨0,1⟩ : QuadInt 0 15) ∧ c = ⟨0,-1⟩) := by sorry





end D1Bound5
end
