-- Prove2me | Theorems.Thm_APFPaper5_K1_sharedCost_le_left
-- name    : APFPaper5.K1.sharedCost_le_left
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:43:33.187288+00:00
-- url     : https://prove2.me/theorems/b9588a51-a9fe-440d-91b5-f2083fd09f61
-- title:
--   One-sided cost monotonicity bounds shared cost by the first cost
-- statement:
--   Let cost be any real-valued function on finite families S,T. Assume h: cost(T)≤cost(S∪T). Then sharedCost(S,T)≤cost(S). This is a conditional numerical bound with no assumption of global cost monotonicity or nonnegative shared cost.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_shared_cost.lean:56; C:/Users/brook/Dev/apf-codebase/apf/delta_calculus.py, 1906-2141; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 1772-1792

import Definitions.Def_APFPaper5_K1_SharedCost
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
universe u v
variable {D : Type u} [DecidableEq D]

theorem APFPaper5.K1.sharedCost_le_left (cost : Finset D → ℝ) (S T : Finset D)
    (h : cost T ≤ cost (S ∪ T)) : sharedCost cost S T ≤ cost S := by sorry
