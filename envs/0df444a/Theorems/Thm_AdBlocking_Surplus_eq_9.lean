-- Prove2me | Theorems.Thm_AdBlocking_Surplus_eq_9
-- name    : AdBlocking.Surplus.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:42.707568+00:00
-- url     : https://prove2.me/theorems/5b3e9b3b-7738-4285-bfd1-e25bcfd54c93
-- title:
--   Equation (9), p. 42 (PDF 43) — the publisher's revenue lost to the adblocker at fixed quality
-- statement:
--   In the same model, with $0<r\le1$, $0\le t\le r/(1+r)$, quality $q>0$, ad level $A^\star=q/(1+r)$, adblocker limit $0\le V\le q/(1+r)$ and support bound $\bar\kappa\ge q/(1+r)-V$, the publisher's benchmark revenue $p_aA^\star D(q,A^\star)$ minus its revenue with the adblocker (which comes only from visitors who do not download, since the adblocker extracts all downloader revenue) equals
--
--   $$\frac{(r^2+4r+1)\bigl(q-(1+r)V\bigr)\,q\,p_a}{6\bar\kappa(1+r)^3(1-t)}.$$
--
--   Substituting the adblocker's optimal limit turns this into the quadratic quality penalty behind Proposition 2.
--
--   **Formalization Note** Revenue with the adblocker is read off `pubProfitAB` by adding back the quality cost $cq^2$. Unlike (6), no lower bound $V\ge qt/r$ is needed. The support bound is the upper limit of the page's $\kappa$-integral.
-- source:
--   Gritckevich, Katona & Sarvary, Ad Blocking, SSRN 3100524 (version of March 7, 2021), p. 42 (PDF 43), proof of Proposition 2, equations (8)–(9)

import Mathlib
import Definitions.Def_AdBlocking_Surplus_Model

namespace AdBlocking.Surplus

theorem eq_9 :
    ∀ pa c r t κbar q V : ℝ, Standing pa c r t → t ≤ r / (1 + r) →
      0 < q → 0 < κbar → 0 ≤ V → V ≤ q / (1 + r) →
      q / (1 + r) - V ≤ κbar →
      benchRev pa r t q (q / (1 + r)) -
          (pubProfitAB pa c r t κbar q (q / (1 + r)) V + c * q ^ 2) =
        (r ^ 2 + 4 * r + 1) * (q - (1 + r) * V) * q * pa /
          (6 * κbar * (1 + r) ^ 3 * (1 - t)) := by sorry

end AdBlocking.Surplus
