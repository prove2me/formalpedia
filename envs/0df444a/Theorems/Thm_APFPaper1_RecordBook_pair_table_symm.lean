-- Prove2me | Theorems.Thm_APFPaper1_RecordBook_pair_table_symm
-- name    : APFPaper1.RecordBook.pair_table_symm
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:21:04.399829+00:00
-- url     : https://prove2.me/theorems/49d5c65c-39e7-47da-8455-d793eb295f26
-- title:
--   A table of two-sided sandwich numbers is symmetric
-- statement:
--   The setting is a ring equipped with a real algebra structure. Marks and their sandwich scalar relations are supplied algebraic data, not reconstructed from the declared APF inputs. The conclusion concerns those exact data and does not assert that any physical interface realizes them. The statement requires neither finite indexing nor idempotence. It proves symmetry of this supplied table, not the physical existence, positivity or admissibility of such pair numbers. Let pᵢ be a family of nonzero elements of a real algebra and cᵢⱼ a real table. Suppose every ordered pair satisfies pᵢpⱼpᵢ = cᵢⱼ pᵢ. Then cᵢⱼ = cⱼᵢ for every pair of indices. The universal ordered-pair hypothesis supplies both relations needed for each comparison. Source: November 12 symmetry ruling; Paper 5 Supplement v7.33, lines 312–350, for the separate physical-score obligation.
-- source:
--   Theorems/Thm_APFPaper1_pair_number_symm.lean, declaration at line 54 (Sib v15; source-scoped review). November 12 symmetry ruling; Paper 5 Supplement v7.33, lines 312–350, for the separate physical-score obligation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Basic

set_option autoImplicit false
namespace APFPaper1.RecordBook
end APFPaper1.RecordBook
open APFPaper1.RecordBook
universe uA uI
variable {A : Type uA} [Ring A] [Algebra ℝ A]

theorem APFPaper1.RecordBook.pair_table_symm {ι : Type uI} (p : ι → A) (c : ι → ι → ℝ) (hp0 : ∀ i, p i ≠ 0)
    (hrel : ∀ i j, p i * p j * p i = c i j • p i) : ∀ i j, c i j = c j i := by sorry
