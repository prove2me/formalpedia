-- Prove2me | Theorems.Thm_AdBlocking_Surplus_cdelta_r0
-- name    : AdBlocking.Surplus.cdelta_r0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:56.41804+00:00
-- url     : https://prove2.me/theorems/6a126a44-d0d4-4232-9666-829da63963f2
-- title:
--   Proof of Proposition 3, p. 44 (PDF 45) — C_Δ(r,0) < C₀(r,0)G(r,0) for every r, with its model meaning
-- statement:
--   Let $0<r\le1$ and $t=0$ (quality sensitivity uniform on $[0,1]$). With $F_0$, $C_\Delta(r,0)$ and $G(r,0)$ the closed forms defined in `TZero` and $C_0(r,0)=(1+r+r^2)/(6(1+r)^2)$:
--
--   1. For every $p_a,c>0$, quality $q>0$ and support bound $\bar\kappa\ge q$, at a benchmark-optimal ad level $A$, the adblocker's optimal limits are exactly $V=qF_0(r)$.
--   2. At such $A$ and an optimal $V$, consumer surplus and the publisher's profit with the adblocker are
--   $$CS_{AB}=qC_0(r,0)+q^2\frac{C_\Delta(r,0)}{\bar\kappa},\qquad \Pi=\frac{qp_a}{2(1+r)}-\frac{p_aG(r,0)q^2}{4(1+r)\bar\kappa}-cq^2.$$
--   3. The coefficients satisfy
--   $$C_\Delta(r,0)<C_0(r,0)\,G(r,0).$$
--
--   Item 3 is the case $t=0$ of the condition that decides the sign in Proposition 3: consumer surplus with the adblocker stays below the benchmark at every $\bar\kappa$. Items 1–2 identify the three closed forms with the model's optimal limit, surplus multiplier and quality-penalty coefficient.
--
--   **Formalization Note** The page states the inequality weakly ("$\le$"); it holds strictly on $(0,1]$ (numerically the gap is at least about $0.042$), and the strict form is what the goal's first clause needs. The profit identity in item 2 is the page's objective with $V^\star$ substituted (p. 42), written so that maximizing it in $q$ yields the $G(r,0)$ of (10).
-- source:
--   Gritckevich, Katona & Sarvary, Ad Blocking, SSRN 3100524 (version of March 7, 2021), p. 44 (PDF 45), proof of Proposition 3 (C_Δ(r,0) display and 'C_Δ(r,0) ≤ C₀(r,0)G(r,0), for any r'); p. 42 (PDF 43) equation (7); pp. 42–43 (PDF 43–44) objective and equation (10)

import Mathlib
import Definitions.Def_AdBlocking_Surplus_Model
import Definitions.Def_AdBlocking_Surplus_C0
import Definitions.Def_AdBlocking_Surplus_TZero

namespace AdBlocking.Surplus

theorem cdelta_r0 :
    ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∀ pa c κbar q A V : ℝ, Standing pa c r 0 → 0 < q → q ≤ κbar →
        IsBenchAdBest pa r 0 q A →
        (IsAdblockBest pa r 0 κbar q A V ↔ V = q * F0 r)) ∧
      (∀ pa c κbar q A V : ℝ, Standing pa c r 0 → 0 < q → q ≤ κbar →
        IsBenchAdBest pa r 0 q A → IsAdblockBest pa r 0 κbar q A V →
        csAB r 0 κbar q A V = q * C0 r 0 + q ^ 2 * CDelta0 r / κbar ∧
        pubProfitAB pa c r 0 κbar q A V =
          q * pa / (2 * (1 + r)) - pa * G0 r * q ^ 2 / (4 * (1 + r) * κbar) -
            c * q ^ 2) ∧
      CDelta0 r < C0 r 0 * G0 r := by sorry

end AdBlocking.Surplus
