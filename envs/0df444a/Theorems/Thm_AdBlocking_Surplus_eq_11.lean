-- Prove2me | Theorems.Thm_AdBlocking_Surplus_eq_11
-- name    : AdBlocking.Surplus.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:42.732845+00:00
-- url     : https://prove2.me/theorems/91d9c824-2168-4880-9bbb-cef7a67ce5f7
-- title:
--   Equation (11) — fixed-quality consumer surplus
-- statement:
--   For each admissible $(r,t)$ there is a positive coefficient $C_\Delta(r,t)$ independent of quality and the download-cost support. At positive quality $q$, with a benchmark-optimal ad volume and an adblocker-optimal limit, consumer surplus satisfies
--
--   $$CS_{NA}=qC_0(r,t),\qquad CS_{AB}=qC_0(r,t)+\frac{q^2C_\Delta(r,t)}{\bar\kappa}.$$
--
--   The second term is the direct gain from ad blocking at fixed quality. Its competition with the quality reduction determines the sign of the equilibrium comparison.
--
--   **Formalization Note** The source's large-support assumption is made explicit as $\bar\kappa\ge q$. $C_0$ uses the corrected first branch described in its definition.
-- source:
--   Gritckevich, Katona & Sarvary, Ad Blocking, SSRN 3100524 (version of March 7, 2021), pp. 43–44 (PDF 44–45), equation (11) and proof of Proposition 3

import Mathlib
import Definitions.Def_AdBlocking_Surplus_Model
import Definitions.Def_AdBlocking_Surplus_C0

namespace AdBlocking.Surplus

theorem eq_11 :
    ∃ CΔ : ℝ → ℝ → ℝ,
      ∀ pa c r t : ℝ, Standing pa c r t →
        0 < CΔ r t ∧
        ∀ q κbar A V : ℝ, 0 < q → q ≤ κbar →
          IsBenchAdBest pa r t q A →
          IsAdblockBest pa r t κbar q A V →
          csNA r t q A = q * C0 r t ∧
          csAB r t κbar q A V = q * C0 r t + q ^ 2 * CΔ r t / κbar := by sorry

end AdBlocking.Surplus
