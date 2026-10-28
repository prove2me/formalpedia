-- Prove2me | Theorems.Thm_D1Bound5_eisenstein_exceptional_pair_extension_trace_zero
-- name    : D1Bound5.eisenstein_exceptional_pair_extension_trace_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:53:20.066064+00:00
-- url     : https://prove2.me/theorems/4258eaed-2376-412a-8675-e5fd3f5bc0c0
-- title:
--   Eisenstein exceptional pair extension trace zero
-- statement:
--   Every common extension of the exceptional Eisenstein unit pair (-ω,1-ω), whose product is -1, has zero trace. No bound on the extension or on its square roots is assumed.
-- source:
--   D1Bound5/EisensteinExceptionalPair.lean, lines 6-34, SHA-256 fec9949d6b0e083b0e0e0a45fd489ab00443fa8d7608258ece4a624254276af4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.eisenstein_exceptional_pair_extension_trace_zero
    (z : QuadInt 1 1)
    (hr : ∃ r : QuadInt 1 1, r*r = (⟨0,-1⟩ : QuadInt 1 1)*z+1)
    (hs : ∃ s : QuadInt 1 1, s*s = (⟨1,-1⟩ : QuadInt 1 1)*z+1) :
    2*z.re+z.im = 0 := by sorry

end D1Bound5
end
