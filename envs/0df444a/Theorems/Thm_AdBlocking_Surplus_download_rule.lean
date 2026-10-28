-- Prove2me | Theorems.Thm_AdBlocking_Surplus_download_rule
-- name    : AdBlocking.Surplus.download_rule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:39.333661+00:00
-- url     : https://prove2.me/theorems/2322abee-ce6c-4558-abc4-3424ab385bf3
-- title:
--   Proof of Proposition 1, p. 41 (PDF 42) — who downloads the adblocker when A = q/(1+r)
-- statement:
--   Fix the ad-sensitivity lower bound $r>0$, a quality $q>0$, the benchmark ad level $A=q/(1+r)$ and an adblocker limit $V$ with $0\le V<q/(1+r)$. A consumer with quality sensitivity $\vartheta$, ad sensitivity $\gamma$ and download cost $\kappa$ downloads the adblocker (strictly prefers the utility $\vartheta q-\gamma V-\kappa$ to $\max(\vartheta q-\gamma A,0)$) if and only if
--
--   $$\gamma>\frac{(1+r)\kappa}{q-V(1+r)}\qquad\text{and}\qquad \vartheta>\frac{\kappa}{q}+\gamma\frac{V}{q}.$$
--
--   The first inequality says the consumer prefers ad level $V$ (after paying $\kappa$) to ad level $A$; the second says the utility with the adblocker is positive. This describes the download region whose mass gives the adblocker's payoff (6).
--
--   **Formalization Note** The download decision uses the strict inequality of the page. The equivalence is stated for every real $(\vartheta,\gamma,\kappa)$, not only on the support.
-- source:
--   Gritckevich, Katona & Sarvary, Ad Blocking, SSRN 3100524 (version of March 7, 2021), p. 41 (PDF 42), proof of Proposition 1, download rule

import Mathlib
import Definitions.Def_AdBlocking_Surplus_Model

namespace AdBlocking.Surplus

theorem download_rule :
    ∀ r q V θ γ κ : ℝ, 0 < r → 0 < q → 0 ≤ V → V < q / (1 + r) →
      (downloads q (q / (1 + r)) V θ γ κ ↔
        (1 + r) * κ / (q - V * (1 + r)) < γ ∧ κ / q + γ * V / q < θ) := by sorry

end AdBlocking.Surplus
