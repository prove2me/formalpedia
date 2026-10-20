-- Prove2me | Theorems.Thm_AdBlocking_Surplus_proposition_1
-- name    : AdBlocking.Surplus.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:43.047928+00:00
-- url     : https://prove2.me/theorems/b80e1ca4-8fac-40b5-93dc-b2c7e531dbb5
-- title:
--   Proposition 1 — optimal adblocker limit
-- statement:
--   There is a function $F(r,t)$ such that, at any fixed positive quality $q$ and any sufficiently large download-cost support $\bar\kappa$, the adblocker's unique revenue-maximizing nonnegative ad limit is
--
--   $$V^*=qF(r,t)\le A^*(q)/2.$$
--
--   The multiplier $F$ is weakly decreasing in $r$ and weakly increasing in $t$. It approaches $1-1/\sqrt3$ as $r\downarrow0$ at $t=0$, and $F(r,1)=1/2$ for $0<r\le1$. This result identifies the ad relief received by downloaders at fixed quality.
--
--   **Formalization Note** The ad level may be any benchmark maximizer; the cost-support bound $\bar\kappa\ge q$ makes the paper's large-support calculation valid. The monotonicity claims use weak order at endpoints.
-- source:
--   Gritckevich, Katona & Sarvary, Ad Blocking, SSRN 3100524 (version of March 7, 2021), p. 17 (PDF 18), Proposition 1; pp. 40–42 (PDF 41–43), proof and equation (7)

import Mathlib
import Definitions.Def_AdBlocking_Surplus_Model

open Filter Topology

namespace AdBlocking.Surplus

theorem proposition_1 :
    ∃ F : ℝ → ℝ → ℝ,
      (∀ pa c r t κbar q A V : ℝ,
        Standing pa c r t → 0 < q → q ≤ κbar →
        IsBenchAdBest pa r t q A →
        (IsAdblockBest pa r t κbar q A V ↔ V = q * F r t) ∧
        q * F r t ≤ A / 2) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        AntitoneOn (fun r => F r t) (Set.Ioc 0 1)) ∧
      (∀ r : ℝ, 0 < r → r ≤ 1 →
        MonotoneOn (F r) (Set.Icc 0 1)) ∧
      Tendsto (fun r => F r 0) (𝓝[>] (0 : ℝ)) (𝓝 (1 - 1 / Real.sqrt 3)) ∧
      (∀ r : ℝ, 0 < r → r ≤ 1 → F r 1 = 1 / 2) := by sorry

end AdBlocking.Surplus
