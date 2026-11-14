-- Prove2me | Theorems.Thm_APFPaper1_RecordBook_pair_number_symm
-- name    : APFPaper1.RecordBook.pair_number_symm
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:19:33.940468+00:00
-- url     : https://prove2.me/theorems/4e02b498-80b3-4107-908a-a34ddafccec3
-- title:
--   Two nonzero marks have the same sandwich scalar in either order
-- statement:
--   The setting is a ring equipped with a real algebra structure. Marks and their sandwich scalar relations are supplied algebraic data, not reconstructed from the declared APF inputs. The conclusion concerns those exact data and does not assert that any physical interface realizes them. Equality of scalars here does not supply reversal of admitted processes, an admissible role-exchange map, or a bound placing the common scalar between zero and one. Let p and q be nonzero elements of a real algebra. If pqp = c p and qpq = c′ q, then c equals c′. Neither idempotence nor commutativity is assumed. Both ordered sandwich relations are required, and their existence is not established by the theorem. Source: November 12 symmetry ruling; Paper 5 Supplement v7.33, lines 312–350, for the separate physical-score obligation.
-- source:
--   Theorems/Thm_APFPaper1_pair_number_symm.lean, declaration at line 37 (Sib v15; source-scoped review). November 12 symmetry ruling; Paper 5 Supplement v7.33, lines 312–350, for the separate physical-score obligation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Basic

set_option autoImplicit false
namespace APFPaper1.RecordBook
end APFPaper1.RecordBook
open APFPaper1.RecordBook
universe uA uI
variable {A : Type uA} [Ring A] [Algebra ℝ A]

theorem APFPaper1.RecordBook.pair_number_symm (p q : A) (c c' : ℝ) (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hrel : p * q * p = c • p) (hrel' : q * p * q = c' • q) : c = c' := by sorry
