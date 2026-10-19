-- Prove2me | Theorems.Thm_FairProxy_ClosedFormDD_endpoint_attainment
-- name    : FairProxy.ClosedFormDD.endpoint_attainment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:08.51741+00:00
-- url     : https://prove2.me/theorems/b8bd3af6-5bf5-4d08-9d2a-b3420e081341
-- title:
--   Proof of Proposition 7, p. 15 — attainment of both disparity endpoints
-- statement:
--   For valid observed marginals and positive probabilities of both protected groups, both proposed Fréchet endpoint values occur as demographic disparities of compatible full joint laws:
--
--   $$
--   \mu(a;w^L)-\mu(b;w^U)\in\Delta_{DD}(\mathcal P_D),
--   \qquad
--   \mu(a;w^U)-\mu(b;w^L)\in\Delta_{DD}(\mathcal P_D).
--   $$
--
--   Endpoint attainment supplies the sharpness behind the interval in Proposition 7.
--
--   **Formalization Note** The paper's sentence claiming that the whole vector $(w^L_a,w^U_b)$ satisfies the law of total probability is false in general. A feasible weight can agree with that vector on the $\hat Y=1$ cells, which are the only cells entering $\mu$, while its $\hat Y=0$ cells satisfy the remaining marginal constraints. This item asserts the valid endpoint consequence.
-- source:
--   Kallus, Mao & Zhou, Assessing Algorithmic Fairness with Unobserved Protected Class Using Data Combination, arXiv:1906.00285v2, p. 15, proof of Proposition 7, final sentence before proof end (corrected endpoint consequence)

import Mathlib
import Definitions.Def_FairProxy_ClosedFormDD_Model

namespace FairProxy.ClosedFormDD

/-- Proof of Proposition 7, p. 15: both numerical Fréchet endpoints are attained
by consistent joints. The printed whole-weight feasibility claim needs correction. -/
theorem endpoint_attainment {Z : Type*} [MeasurableSpace Z]
    (M : Marginals Z) (hM : M.Valid)
    (ha : 0 < probA M .a) (hb : 0 < probA M .b) :
    (mu M .a (wL M) - mu M .b (wU M)) ∈ PIsetDD M ∧
      (mu M .a (wU M) - mu M .b (wL M)) ∈ PIsetDD M := by sorry

end FairProxy.ClosedFormDD
