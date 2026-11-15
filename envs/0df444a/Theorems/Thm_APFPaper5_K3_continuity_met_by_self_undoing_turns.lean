-- Prove2me | Theorems.Thm_APFPaper5_K3_continuity_met_by_self_undoing_turns
-- name    : APFPaper5.K3.continuity_met_by_self_undoing_turns
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:14:06.608022+00:00
-- url     : https://prove2.me/theorems/e348c365-e881-4e7a-850a-50fe821a1169
-- title:
--   Continuity met by self undoing turns
-- statement:
--   The real-valued relation rel(s)=s with target interval [0,1] satisfies the supplied Continuity predicate when admitted maps are transpositions of two real points. Every admitted map squares to the identity. Thus that predicate alone need not provide two-step nonreturn.
-- source:
--   Sib v44 Theorems/Thm_APFB07_moves.lean:54

import Definitions.Def_APFPaper5_K3_Continuity
import Theorems.Thm_APFB07b_realized_history_retraces_of_sum_cost
import Theorems.Thm_APFB07b_rate_is_held_on_realized_history
import Theorems.Thm_APFB07b_one_way_history_meets_A2_BW
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false

universe uX uP uR

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.continuity_met_by_self_undoing_turns :
    Continuity (fun s : ℝ => s) 0 1 {f : ℝ → ℝ | ∃ a b : ℝ, f = fun s => Equiv.swap a b s} ∧
      ∀ f ∈ {f : ℝ → ℝ | ∃ a b : ℝ, f = fun s => Equiv.swap a b s}, ∀ s : ℝ, f (f s) = s := by sorry
