-- Prove2me | Theorems.Thm_CourierDispatch_Endogenous_demand_drop_at_switch
-- name    : CourierDispatch.Endogenous.demand_drop_at_switch
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:06.54098+00:00
-- url     : https://prove2.me/theorems/06163482-bcf0-4964-828a-5a918c4a7f98
-- title:
--   Proof of Proposition 3 — batch optimal demand exceeds dedicated at the switch
-- statement:
--   Let $c,r>0$ and $C_B\in[0.58,0.59]$. Suppose batch and dedicated delivery have equal optimal limiting revenue. For any optimal batch demand $\lambda_B\in(0,2\mu_B)$ and any optimal dedicated demand $\lambda_F\in[0,\mu_D)$,
--   $$
--   \lambda_F<\lambda_B.
--   $$
--   Thus changing from batch to dedicated at the revenue tie lowers the demand rate. This comparison supports the discontinuity claims in Propositions 3 and 4.
--
--   **Formalization Note** The Lean name `lam` denotes $\lambda$. The hypotheses require both demands to attain their respective optima, rather than silently assuming attainment at all parameter values. The proof's displayed closed-form difference has an inconsistent factor $T_B$ under its last square root; this theorem states the comparison asserted by its prose.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), Online Appendix p. 3, proof of Proposition 3, after (A.7)

import Mathlib
import Definitions.Def_CourierDispatch_Endogenous_Setting

namespace CourierDispatch.Endogenous

theorem demand_drop_at_switch (CB c r lB lF : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB)
    (hc : 0 < c) (hr : 0 < r) (htie : OptB CB c r = OptD c r)
    (hB : lB ∈ domB r ∧ VinfB CB c r lB = OptB CB c r)
    (hF : lF ∈ domD r ∧ VinfD c r lF = OptD c r) :
    lF < lB := by sorry

end CourierDispatch.Endogenous
