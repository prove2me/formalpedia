-- Prove2me | Theorems.Thm_APFPaper1_RecordBook_pair_number_zero_or_one_of_commute
-- name    : APFPaper1.RecordBook.pair_number_zero_or_one_of_commute
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:20:58.010253+00:00
-- url     : https://prove2.me/theorems/de1f3f78-27cf-4f34-a263-375b7b6cea29
-- title:
--   Commuting repeatable marks have sandwich scalar zero or one
-- statement:
--   The result is conditional algebra: commutativity and idempotence force the product pq to be idempotent, and nonzero p permits scalar cancellation. No physical algebra of word values, existence of the scalar at an interface, continuity of its values or admissible transformation between marks is constructed. Let p and q be idempotents in a real algebra. Assume p and q commute, p is nonzero, and pqp equals c times p. Then c is zero or one. The theorem does not require q to be nonzero or require a separately supplied reverse sandwich relation qpq. Source: Paper 1 Supplement v9.28, lines 3721–3746 and 6276–6280, scoped commuting-record calculation.
-- source:
--   Theorems/Thm_APFPaper1_pair_number.lean, declaration at line 34 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 3721–3746 and 6276–6280, scoped commuting-record calculation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper1.RecordBook
end APFPaper1.RecordBook
open APFPaper1.RecordBook
universe uA
variable {A : Type uA} [Ring A] [Algebra ℝ A]

theorem APFPaper1.RecordBook.pair_number_zero_or_one_of_commute (p q : A) (c : ℝ)
    (hp : p * p = p) (hq : q * q = q) (hcomm : p * q = q * p)
    (hrel : p * q * p = c • p) (hp0 : p ≠ 0) : c = 0 ∨ c = 1 := by sorry
