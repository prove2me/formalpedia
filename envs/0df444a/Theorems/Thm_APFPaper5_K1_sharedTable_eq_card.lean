-- Prove2me | Theorems.Thm_APFPaper5_K1_sharedTable_eq_card
-- name    : APFPaper5.K1.sharedTable_eq_card
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:45:31.887668+00:00
-- url     : https://prove2.me/theorems/e65c232a-8ec6-4b1e-9f41-3e8731990c2f
-- title:
--   SharedTable is exactly the size of the family intersection
-- statement:
--   For a finite distinction type and supplied finite families R(i), sharedTable(R,i,j)=|R(i)∩R(j)|, with the natural-number count viewed as a real number. The theorem identifies the unit-weight Boolean overlap definition with the intersection cardinality. It does not normalize the count or give a physical frequency.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_shared_count_card.lean:22; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_two_adoptions_2026-11-12.md, 1

import Definitions.Def_APFPaper5_K1_SharedCount
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
universe u v
variable {ι : Type u} {D : Type v} [Fintype D] [DecidableEq D]

theorem APFPaper5.K1.sharedTable_eq_card (fam : ι → Finset D) (i j : ι) :
    sharedTable fam i j = ((fam i ∩ fam j).card : ℝ) := by sorry
