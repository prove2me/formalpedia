-- Prove2me | Theorems.Thm_CourierDispatch_Endogenous_batch_optimum
-- name    : CourierDispatch.Endogenous.batch_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:57.224367+00:00
-- url     : https://prove2.me/theorems/c2b1db3a-3f8a-442c-ab45-4ba93e7f87a3
-- title:
--   (A.4), corrected (A.6) — batch optimal demand and revenue
-- statement:
--   Let $c,r,C_B>0$, $cr<T_B$, and set
--   $$
--   \lambda_B^\infty=\frac{T_B}{r}\left(1-\frac{\sqrt3\,crC_B}{\sqrt{crC_B[3T_B+cr(3C_B-T_B)]}}\right).
--   $$
--   This demand belongs to $(0,2\mu_B)$ and attains the greatest limiting batch revenue there. Its value is
--   $$
--   V_B^\infty(\lambda_B^\infty)=c\left(2C_B-\frac12-\frac{T_B}{3}\right)+\frac{T_B}{r}
--      -\frac{2}{3r}\sqrt{3crC_B[3T_B+cr(3C_B-T_B)]}.
--   $$
--   This is the batch branch needed to locate the revenue switch.
--
--   **Formalization Note** The Lean name `lam` denotes $\lambda$. The printed (A.6) has `4/r` in place of $2/(3r)$ and `3B` in place of $3C_B$; the displayed expression here is the corrected value verified against the objective in (A.3). The printed batch domain includes zero, where $W_B$ is singular, so the formal domain is open at zero.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), Online Appendix p. 2, (A.4), (A.6) (corrected as documented in paper.md)

import Mathlib
import Definitions.Def_CourierDispatch_Endogenous_Setting

namespace CourierDispatch.Endogenous

theorem batch_optimum (CB c r : ℝ) (hCB : 0 < CB) (hc : 0 < c) (hr : 0 < r)
    (hsmall : c * r < CourierDispatch.Exogenous.TB) :
    let lB := CourierDispatch.Exogenous.TB / r *
      (1 - Real.sqrt 3 * (c * r * CB) /
        Real.sqrt (c * r * CB * (3 * CourierDispatch.Exogenous.TB + c * r * (3 * CB - CourierDispatch.Exogenous.TB))))
    lB ∈ domB r ∧
    IsGreatest (VinfB CB c r '' domB r) (VinfB CB c r lB) ∧
    VinfB CB c r lB =
      c * (2 * CB - 1 / 2 - CourierDispatch.Exogenous.TB / 3) + CourierDispatch.Exogenous.TB / r -
        2 / (3 * r) * Real.sqrt (3 * c * r * CB * (3 * CourierDispatch.Exogenous.TB + c * r * (3 * CB - CourierDispatch.Exogenous.TB))) := by sorry

end CourierDispatch.Endogenous
