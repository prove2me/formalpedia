-- Prove2me | Theorems.Thm_FBAComp_AmazonGain_lemma_A_1
-- name    : FBAComp.AmazonGain.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:01.922999+00:00
-- url     : https://prove2.me/theorems/bb996db3-b016-4565-bc1a-63efbc86c2de
-- title:
--   Lemma A.1, p. 34 — unique no-FBA equilibrium
-- statement:
--   For any real cross-service sensitivity $\eta$ under the standing parameter regime, the no-FBA game has exactly the wholesale price and retail-price pair printed in Lemma A.1:
--
--   $$\operatorname{Eq}_N(\eta,w,p_A,p_S)\iff (w,p_A,p_S)=(w_N^*,p_{A,N}^*,p_{S,N}^*).$$
--
--   The biconditional asserts both existence and uniqueness, and supplies the benchmark for the later profit comparisons.
-- source:
--   Lai, Liu, Xiao & Zhao, “Fulfilled by Amazon”, SSRN preprint 3270958 (PDF of 2021-10-08), p. 34, Lemma A.1

import Mathlib
import Definitions.Def_FBAComp_AmazonGain_ClosedForms

namespace FBAComp.AmazonGain

/-- Lemma A.1, p. 34: the no-FBA game has exactly the printed equilibrium. -/
theorem lemma_A_1 (P : Params) (hP : P.Standing) (η w pA pS : ℝ) :
    IsEqN P η w pA pS ↔
      w = wN_star P η ∧ pA = pAN_star P η ∧ pS = pSN_star P η := by sorry

end FBAComp.AmazonGain
