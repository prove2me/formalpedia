-- Prove2me | Theorems.Thm_AdBlocking_Surplus_eq_6
-- name    : AdBlocking.Surplus.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:48.342494+00:00
-- url     : https://prove2.me/theorems/6cb2bc5f-c8ba-45f8-b27d-12b4fa5ab59a
-- title:
--   Equation (6), p. 41 (PDF 42) — the adblocker's payoff T(q,V) when t ≤ r/(1+r) and V ≥ qt/r
-- statement:
--   Consider the ad-blocking model with ad price $p_a>0$, quality sensitivity $\vartheta\sim U(t,1)$, ad sensitivity $\gamma\sim U(r,1)$ and download cost $\kappa\sim U(0,\bar\kappa)$, independent, with $0<r\le1$ and $0\le t\le r/(1+r)$. Let the publisher's quality be $q>0$ and its ad level the benchmark optimum $A^\star=q/(1+r)$. For an adblocker limit $V$ with $qt/r\le V\le q/(1+r)$ and a support bound $\bar\kappa\ge q/(1+r)-V$, the adblocker's payoff, $T(q,V)=p_aV$ times the mass of consumers who download, equals
--
--   $$T(q,V)=p_aV\,\frac{\bigl(q-V(1+r)\bigr)\bigl(q(2+5r+2r^2)-V(1+r)(1+r+r^2)\bigr)}{6q(1+r)^2(1-t)\bar\kappa}.$$
--
--   This closed form is the objective the adblocker maximizes in Proposition 1 on the segment $V\ge qt/r$.
--
--   **Formalization Note** The payoff is the model's iterated expectation, not the formula. The bound $\bar\kappa\ge q/(1+r)-V$ is the upper limit of the page's $\kappa$-integral: it keeps every download cost that produces a download inside the support. $t\le r/(1+r)$ implies $t\le 1/2$, so $1-t>0$.
-- source:
--   Gritckevich, Katona & Sarvary, Ad Blocking, SSRN 3100524 (version of March 7, 2021), p. 41 (PDF 42), proof of Proposition 1, equation (6) with (4)–(5)

import Mathlib
import Definitions.Def_AdBlocking_Surplus_Model

namespace AdBlocking.Surplus

theorem eq_6 :
    ∀ pa c r t κbar q V : ℝ, Standing pa c r t → t ≤ r / (1 + r) →
      0 < q → 0 < κbar → q * t / r ≤ V → V ≤ q / (1 + r) →
      q / (1 + r) - V ≤ κbar →
      adblockerPayoff pa r t κbar q (q / (1 + r)) V =
        pa * V * (q - V * (1 + r)) *
            (q * (2 + 5 * r + 2 * r ^ 2) - V * (1 + r) * (1 + r + r ^ 2)) /
          (6 * q * (1 + r) ^ 2 * (1 - t) * κbar) := by sorry

end AdBlocking.Surplus
