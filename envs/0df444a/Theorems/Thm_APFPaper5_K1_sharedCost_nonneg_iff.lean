-- Prove2me | Theorems.Thm_APFPaper5_K1_sharedCost_nonneg_iff
-- name    : APFPaper5.K1.sharedCost_nonneg_iff
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:44:18.310193+00:00
-- url     : https://prove2.me/theorems/f7470121-510f-4689-bf1e-fcb474fcce0b
-- title:
--   Shared cost is nonnegative exactly when joint cost is subadditive
-- statement:
--   For any real-valued cost on finite families S,T, sharedCost(S,T)≥0 if and only if cost(S∪T)≤cost(S)+cost(T). The result is an exact rearrangement of sharedCost(S,T)=cost(S)+cost(T)−cost(S∪T), with no sign or monotonicity assumption on cost. It characterizes when joint service gives a nonnegative discount. It does not prove that an arbitrary physical family cost is subadditive, or that its shared-cost expression is an ordered score or a probability.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_shared_cost.lean:61; C:/Users/brook/Dev/apf-codebase/apf/delta_calculus.py, 1906-2141; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 1772-1792

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

theorem APFPaper5.K1.sharedCost_nonneg_iff (cost : Finset D → ℝ) (S T : Finset D) :
    0 ≤ sharedCost cost S T ↔ cost (S ∪ T) ≤ cost S + cost T := by sorry
