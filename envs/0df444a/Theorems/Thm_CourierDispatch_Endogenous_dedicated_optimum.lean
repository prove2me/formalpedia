-- Prove2me | Theorems.Thm_CourierDispatch_Endogenous_dedicated_optimum
-- name    : CourierDispatch.Endogenous.dedicated_optimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:59.322708+00:00
-- url     : https://prove2.me/theorems/28cdf14c-186f-4fbe-b141-87decfbb9c2a
-- title:
--   (A.4)–(A.5) — dedicated optimal demand and revenue
-- statement:
--   Let $c,r>0$, $cr<T_B$, and set
--   $$
--   \lambda_F^\infty=\frac{T_D}{r}\left(1-\frac{crC_D}{\sqrt{crC_D(2T_D+crC_D)}}\right).
--   $$
--   This demand belongs to the dedicated stability range $[0,\mu_D)$, attains the greatest limiting dedicated revenue there, and has value
--   $$
--   V_D^\infty(\lambda_F^\infty)=cC_D+\frac{T_D}{r}-\frac1r\sqrt{crC_D(2T_D+crC_D)}.
--   $$
--   The formula supplies the dedicated branch of the revenue comparison.
--
--   **Formalization Note** The Lean name `lam` denotes $\lambda$. The hypothesis $cr<T_B$ is the one preceding (A.4); the formula remains meaningful over a wider range, which is not claimed here. `IsGreatest` records actual attainment, as asserted by the appendix.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), Online Appendix p. 2, (A.4)–(A.5)

import Mathlib
import Definitions.Def_CourierDispatch_Endogenous_Setting

namespace CourierDispatch.Endogenous

theorem dedicated_optimum (c r : ℝ) (hc : 0 < c) (hr : 0 < r)
    (hsmall : c * r < CourierDispatch.Exogenous.TB) :
    let lF := CourierDispatch.Exogenous.TD / r * (1 - c * r * CourierDispatch.Exogenous.CD / Real.sqrt (c * r * CourierDispatch.Exogenous.CD * (2 * CourierDispatch.Exogenous.TD + c * r * CourierDispatch.Exogenous.CD)))
    lF ∈ domD r ∧
    IsGreatest (VinfD c r '' domD r) (VinfD c r lF) ∧
    VinfD c r lF = c * CourierDispatch.Exogenous.CD + CourierDispatch.Exogenous.TD / r - 1 / r * Real.sqrt (c * r * CourierDispatch.Exogenous.CD * (2 * CourierDispatch.Exogenous.TD + c * r * CourierDispatch.Exogenous.CD)) := by sorry

end CourierDispatch.Endogenous
