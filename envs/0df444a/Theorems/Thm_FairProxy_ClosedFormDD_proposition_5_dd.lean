-- Prove2me | Theorems.Thm_FairProxy_ClosedFormDD_proposition_5_dd
-- name    : FairProxy.ClosedFormDD.proposition_5_dd
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:58.724101+00:00
-- url     : https://prove2.me/theorems/856e4d36-0ca3-4be5-8c51-515cc448f28f
-- title:
--   Proposition 5, p. 14 — demographic disparity as an image of admissible weights
-- statement:
--   Fix valid observed marginals $M$ with $P(A=a)>0$ and $P(A=b)>0$. Let $\mathcal P_D$ be the compatible joint laws, and let $\mathcal W(\mathcal P_D)$ be their induced conditional protected-class weights. The possible demographic disparity values are exactly
--
--   $$
--   \Delta_{DD}(\mathcal P_D)=\{\mu(a;w)-\mu(b;w):w\in\mathcal W(\mathcal P_D)\},
--   \qquad
--   \mu(\alpha;w)=\frac{E[w_\alpha(\hat Y,Z)\hat Y]}{P(A=\alpha)}.
--   $$
--
--   This is the demographic-disparity clause of Proposition 5 for the compatible-joint set used by Proposition 7.
--
--   **Formalization Note** The paper states Proposition 5 for a general set of joints and includes two other disparity measures. This item states its DD instance for $\mathcal P_D$. The positive group masses make both conditional rates well defined.
-- source:
--   Kallus, Mao & Zhou, Assessing Algorithmic Fairness with Unobserved Protected Class Using Data Combination, arXiv:1906.00285v2, p. 14, Proposition 5, DD clause; Appendix B.2, p. 49

import Mathlib
import Definitions.Def_FairProxy_ClosedFormDD_Model

namespace FairProxy.ClosedFormDD

/-- Proposition 5, p. 14, specialized to the DD clause and the consistent-joint set. -/
theorem proposition_5_dd {Z : Type*} [MeasurableSpace Z]
    (M : Marginals Z) (hM : M.Valid)
    (ha : 0 < probA M .a) (hb : 0 < probA M .b) :
    PIsetDD M =
      {d | ∃ w, w ∈ WPD M ∧ mu M .a w - mu M .b w = d} := by sorry

end FairProxy.ClosedFormDD
