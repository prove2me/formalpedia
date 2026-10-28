-- Prove2me | Theorems.Thm_D1Bound5_pairSelectedCachedMaskRejectBool_sound
-- name    : D1Bound5.pairSelectedCachedMaskRejectBool_sound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:54.719965+00:00
-- url     : https://prove2.me/theorems/03aecc98-05ad-4c0c-83c0-ed81ac3c9e99
-- title:
--   Pair Selected Cached Mask Reject Bool sound
-- statement:
--   One genuinely rejecting aligned conjunct makes the entire original cached sieve false. This is a statement about the exact old Boolean, so no signature-validity, mask-validity, or discriminant assumption is needed.
-- source:
--   D1Bound5/PairSelectedCachedMask.lean, lines 14-55, SHA-256 842d5e0cce863d3301c8c65c34a04d2d07c08d156761bf506cdbbebcdd0db1f4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairSelectedCachedMask_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.pairSelectedCachedMaskRejectBool_sound (tau nu : ℤ)
    (sieve : List (ℕ × ℕ)) (xs ys : List (ℕ × ℕ)) (i : ℕ)
    (hcheck : pairSelectedCachedMaskRejectBool tau nu sieve xs ys i = true) :
    pairCachedCoordinateSieveBool tau nu sieve xs ys = false := by sorry

end D1Bound5
end
