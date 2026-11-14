-- Prove2me | Theorems.Thm_APFPaper5_K1_sharedCost_self
-- name    : APFPaper5.K1.sharedCost_self
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:45:18.30713+00:00
-- url     : https://prove2.me/theorems/513059e4-0c78-4808-b4c6-a2a341d27bf3
-- title:
--   A family’s shared cost with itself is its own cost
-- statement:
--   For any real-valued cost on finite families and any family S, sharedCost(S,S)=cost(S). Here sharedCost subtracts the cost of the union from the sum of separate costs. The identity does not require positivity, monotonicity, normalization or a physical score interpretation.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_shared_cost.lean:41; C:/Users/brook/Dev/apf-codebase/apf/delta_calculus.py, 1906-2141; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 1772-1792

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

theorem APFPaper5.K1.sharedCost_self (cost : Finset D → ℝ) (S : Finset D) : sharedCost cost S S = cost S := by sorry
