-- Prove2me | Theorems.Thm_APFPaper1_RecordBook_pair_number_self
-- name    : APFPaper1.RecordBook.pair_number_self
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:19:28.070192+00:00
-- url     : https://prove2.me/theorems/cb06dd7f-d555-4aee-aa91-6a6cd7423539
-- title:
--   A nonzero idempotent has self sandwich scalar one
-- statement:
--   In a real algebra, if p is nonzero and idempotent and ppp = c p, then c = 1. Nonzero p is required for scalar cancellation; no relation to a second mark is involved. Source: November 12 symmetry ruling; Paper 5 Supplement v7.33, lines 312–350, for the separate physical-score obligation.
-- source:
--   Theorems/Thm_APFPaper1_pair_number_symm.lean, declaration at line 59 (Sib v15; source-scoped review). November 12 symmetry ruling; Paper 5 Supplement v7.33, lines 312–350, for the separate physical-score obligation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Basic

set_option autoImplicit false
namespace APFPaper1.RecordBook
end APFPaper1.RecordBook
open APFPaper1.RecordBook
universe uA uI
variable {A : Type uA} [Ring A] [Algebra ℝ A]

theorem APFPaper1.RecordBook.pair_number_self (p : A) (c : ℝ) (hp0 : p ≠ 0) (hp : p * p = p)
    (hrel : p * p * p = c • p) : c = 1 := by sorry
