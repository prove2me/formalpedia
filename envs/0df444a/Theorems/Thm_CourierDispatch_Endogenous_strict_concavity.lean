-- Prove2me | Theorems.Thm_CourierDispatch_Endogenous_strict_concavity
-- name    : CourierDispatch.Endogenous.strict_concavity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:49.753926+00:00
-- url     : https://prove2.me/theorems/d0cb647e-ddf4-4082-8aa3-27bcb40bad24
-- title:
--   (A.3) — strict concavity of the dedicated and batch objectives
-- statement:
--   Fix positive wait cost $c$, radius $r$, and batch variation coefficient $C_B$. On their stable demand ranges, both limiting revenue objectives are strictly concave:
--   $$
--   V_D^\infty\text{ on }[0,\mu_D),\qquad V_B^\infty\text{ on }(0,2\mu_B).
--   $$
--   This gives uniqueness to each attained optimal demand in the threshold analysis.
--
--   **Formalization Note** The Lean name `lam` denotes $\lambda$. The batch domain excludes zero, where the paper's waiting-time formula contains $1/(2\lambda)$; its printed (A.3) includes zero. The theorem states strict concavity, the conclusion supported by the displayed second derivatives on Online Appendix p. 2.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), Online Appendix p. 2, after (A.3)

import Mathlib
import Definitions.Def_CourierDispatch_Endogenous_Setting

namespace CourierDispatch.Endogenous

theorem strict_concavity (CB c r : ℝ) (hCB : 0 < CB) (hc : 0 < c) (hr : 0 < r) :
    StrictConcaveOn ℝ (domD r) (VinfD c r) ∧
    StrictConcaveOn ℝ (domB r) (VinfB CB c r) := by sorry

end CourierDispatch.Endogenous
