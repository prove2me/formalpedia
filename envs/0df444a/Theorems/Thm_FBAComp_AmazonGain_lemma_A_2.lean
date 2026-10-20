-- Prove2me | Theorems.Thm_FBAComp_AmazonGain_lemma_A_2
-- name    : FBAComp.AmazonGain.lemma_A_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:10.548462+00:00
-- url     : https://prove2.me/theorems/a889de3e-db1e-4573-bd7c-3680ce445612
-- title:
--   Lemma A.2, p. 34 — unique FBA subgame outcome
-- statement:
--   For any real $\eta$ and fixed real fee $T$ under the standing parameter regime, the FBA subgame has exactly the wholesale price and retail-price pair printed in Lemma A.2:
--
--   $$\operatorname{Eq}_F(\eta,T,w,p_A,p_S)\iff (w,p_A,p_S)=(w_F^*(T),p_{A,F}^*(T),p_{S,F}^*(T)).$$
--
--   The biconditional gives existence and uniqueness of the subgame outcome needed for Amazon's fee optimization.
-- source:
--   Lai, Liu, Xiao & Zhao, “Fulfilled by Amazon”, SSRN preprint 3270958 (PDF of 2021-10-08), p. 34, Lemma A.2

import Mathlib
import Definitions.Def_FBAComp_AmazonGain_ClosedForms

namespace FBAComp.AmazonGain

/-- Lemma A.2, p. 34: for any fixed fee the FBA subgame has exactly the printed outcome. -/
theorem lemma_A_2 (P : Params) (hP : P.Standing) (η T w pA pS : ℝ) :
    IsSubgameEqF P η T w pA pS ↔
      w = wF_star P η T ∧ pA = pAF_star P η T ∧ pS = pSF_star P η T := by sorry

end FBAComp.AmazonGain
