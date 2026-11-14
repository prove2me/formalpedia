-- Prove2me | Theorems.Thm_APFPaper5_K1_sharedCost_channel_ledger
-- name    : APFPaper5.K1.sharedCost_channel_ledger
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:41:55.27002+00:00
-- url     : https://prove2.me/theorems/0fd8411f-7567-448d-bd62-8bd5992cad0d
-- title:
--   Under channel retention, shared cost counts shared minus new joint channels
-- statement:
--   Supply a finite channel set Ch(X) for each finite family X and define cost(X)=ε|Ch(X)| for a real ε. Assume hCH1: Ch(S)∪Ch(T) is contained in Ch(S∪T). Then sharedCost(S,T)=ε(R−J), where R counts Ch(S)∩Ch(T) and J counts channels in Ch(S∪T) outside the union of marginal channel sets. The identity allows any real ε. Cost proportional to count is built into this model, and the channel-retention hypothesis is explicit; neither is derived for a physical family cost.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_shared_cost.lean:66; C:/Users/brook/Dev/apf-codebase/apf/delta_calculus.py, 1906-2141; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 1772-1792

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

theorem APFPaper5.K1.sharedCost_channel_ledger {Ch : Type v} [DecidableEq Ch] (chan : Finset D → Finset Ch)
    (eps : ℝ) (S T : Finset D) (hCH1 : chan S ∪ chan T ⊆ chan (S ∪ T)) :
    sharedCost (fun X => eps * ((chan X).card : ℝ)) S T =
      eps * (((chan S ∩ chan T).card : ℝ) -
        ((chan (S ∪ T) \ (chan S ∪ chan T)).card : ℝ)) := by sorry
