-- Prove2me | Theorems.Thm_APFPaper5_K1_sharedCost_channel_no_joint
-- name    : APFPaper5.K1.sharedCost_channel_no_joint
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:43:27.249198+00:00
-- url     : https://prove2.me/theorems/6f0c6db4-02d6-46fe-a4b6-446ab0b9eac9
-- title:
--   With no new joint channels, shared cost is the shared-channel weight
-- statement:
--   Define cost(X)=ε|Ch(X)| for a supplied finite channel assignment and arbitrary real scale ε. Assume hJ: Ch(S∪T)=Ch(S)∪Ch(T). Then sharedCost(S,T)=ε|Ch(S)∩Ch(T)|. The no-new-joint-channel equality is supplied, and no sign condition on ε is needed.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_shared_cost.lean:84; C:/Users/brook/Dev/apf-codebase/apf/delta_calculus.py, 1906-2141; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 1772-1792

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

theorem APFPaper5.K1.sharedCost_channel_no_joint {Ch : Type v} [DecidableEq Ch] (chan : Finset D → Finset Ch)
    (eps : ℝ) (S T : Finset D) (hJ : chan (S ∪ T) = chan S ∪ chan T) :
    sharedCost (fun X => eps * ((chan X).card : ℝ)) S T =
      eps * ((chan S ∩ chan T).card : ℝ) := by sorry
