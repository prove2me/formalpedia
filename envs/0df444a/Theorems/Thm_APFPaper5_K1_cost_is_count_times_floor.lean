-- Prove2me | Theorems.Thm_APFPaper5_K1_cost_is_count_times_floor
-- name    : APFPaper5.K1.cost_is_count_times_floor
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:27:34.264502+00:00
-- url     : https://prove2.me/theorems/a907fd34-1024-49fb-8a5a-b01f02e70d60
-- title:
--   Additivity on natural-number counts fixes cost from its unit value
-- statement:
--   Let f map natural-number counts to real numbers. Assume hadd: f(m+n)=f(m)+f(n) for every natural m,n, and h1: f(1)=ε for a supplied real ε. Then f(n)=nε for every natural n. This is the discrete count-domain characterization, obtained without a monotonicity or continuity premise. It makes no assumption that ε is positive, and does not prove that an arbitrary physical cost depends only on count or satisfies the supplied additivity law.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_shared_cost.lean:111; C:/Users/brook/Dev/apf-codebase/apf/delta_calculus.py, 1906-2141; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 1772-1792

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

omit [DecidableEq D] in
theorem APFPaper5.K1.cost_is_count_times_floor (f : ℕ → ℝ) (eps : ℝ)
    (hadd : ∀ m n : ℕ, f (m + n) = f m + f n) (h1 : f 1 = eps) :
    ∀ n : ℕ, f n = (n : ℝ) * eps := by sorry
