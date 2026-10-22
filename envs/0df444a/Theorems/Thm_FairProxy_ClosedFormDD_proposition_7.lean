-- Prove2me | Theorems.Thm_FairProxy_ClosedFormDD_proposition_7
-- name    : FairProxy.ClosedFormDD.proposition_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:00.597854+00:00
-- url     : https://prove2.me/theorems/71e9e008-6338-4524-af9e-ceff38b402c4
-- title:
--   Proposition 7, p. 15 — sharp closed interval for demographic disparity
-- statement:
--   Let the observed primary and auxiliary marginals be valid and share a proxy distribution on an arbitrary measurable space. Suppose both protected groups have positive probability. For all full joint laws consistent with those marginals, the set of demographic disparities is exactly
--
--   $$
--   \Delta_{DD}(\mathcal P_D)=
--   [\mu(a;w^L)-\mu(b;w^U),\;\mu(a;w^U)-\mu(b;w^L)].
--   $$
--
--   Here $\mu(\alpha;w)=E[w_\alpha(\hat Y,Z)\hat Y]/P(A=\alpha)$, and $w^L,w^U$ are the Fréchet–Hoeffding weight endpoints of Proposition 7. The equality is sharp: every number in the interval is realized by some compatible full joint.
--
--   **Formalization Note** The model retains the true outcome $Y$ in the full joint and imposes no additional association assumptions. Positive group masses are explicit because conditional probabilities given $A=\alpha$ otherwise lack the paper's meaning. Conditional weight comparisons ignore zero-probability decision cells, while their contributions to $\mu$ vanish.
-- source:
--   Kallus, Mao & Zhou, Assessing Algorithmic Fairness with Unobserved Protected Class Using Data Combination, arXiv:1906.00285v2, p. 15, Proposition 7, Eq. (11)

import Mathlib
import Definitions.Def_FairProxy_ClosedFormDD_Model

namespace FairProxy.ClosedFormDD

/-- Proposition 7, p. 15, equation (11): the sharp closed interval of demographic disparity
values over all joint laws consistent with the two observed marginals. -/
theorem proposition_7 {Z : Type*} [MeasurableSpace Z]
    (M : Marginals Z) (hM : M.Valid)
    (ha : 0 < probA M .a) (hb : 0 < probA M .b) :
    PIsetDD M = Set.Icc
      (mu M .a (wL M) - mu M .b (wU M))
      (mu M .a (wU M) - mu M .b (wL M)) := by sorry

end FairProxy.ClosedFormDD
