-- Prove2me | Theorems.Thm_FlexApproval_Statics_theorem_1_concave
-- name    : FlexApproval.Statics.theorem_1_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:36.405655+00:00
-- url     : https://prove2.me/theorems/c51c8874-49ff-4a6c-a809-27fe4f16437b
-- title:
--   Theorem 1 (first part), p. 12 — the expected net benefit V(α) is concave in α on [0, 1]
-- statement:
--   Under the standing assumptions of the drug-approval model, the expected net benefit
--   $$V(\alpha)=\big(Q_E\,\mathbb E[N_E(\alpha)]-Q_I\,\mathbb E[N_I(\alpha)]\big)\mathrm{WTP}+C_{AE}\lambda_{AE}(\alpha)-C_{AI}\lambda_{AI}(\alpha)-C_{RE}\lambda_{RE}(\alpha)$$
--   is a concave function of the significance level $\alpha$ on $[0,1]$.
--
--   Concavity makes the first-order condition (5) characterize the optimal approval policy and underlies the comparative statics of Proposition 1.
--
--   **Formalization Note** $V$ on $[0,1]$ uses the limit values of the power curve at $\alpha\in\{0,1\}$.
-- source:
--   Bravo, Corcoran & Long, Flexible Drug Approval Policies, SSRN working paper 3027263 (version of 17 Jul 2019), p. 12, Theorem 1 (first part)

import Mathlib
import Definitions.Def_FlexApproval_Statics_Model

namespace FlexApproval.Statics

/-- Theorem 1 (first part), p. 12: the expected net benefit `V(α)` is concave in `α` on `[0, 1]`. -/
theorem theorem_1_concave (P : Params) (hP : P.Standing) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (V P) := by sorry

end FlexApproval.Statics
