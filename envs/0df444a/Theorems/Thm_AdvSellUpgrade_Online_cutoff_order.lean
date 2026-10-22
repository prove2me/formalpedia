-- Prove2me | Theorems.Thm_AdvSellUpgrade_Online_cutoff_order
-- name    : AdvSellUpgrade.Online.cutoff_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:39.858478+00:00
-- url     : https://prove2.me/theorems/37b4e415-c59a-4c07-9458-d9504a4581c3
-- title:
--   §5.1, p. 15 — the two optimal cutoffs satisfy 0 < c(λₕ) < c(λₗ) < c̄
-- statement:
--   Let $0<\lambda_l<\lambda_h<\mu$ and $\bar c>0$, and let
--   $$c(\lambda)=\frac{\bigl(\sqrt{\mu(\mu-\lambda)}-(\mu-\lambda)\bigr)\bar c}{\lambda}$$
--   be the optimal single-rate delay-sensitivity cutoff. Then
--   $$0<c(\lambda_h)<c(\lambda_l)<\bar c .$$
--
--   In words: the optimal cutoff lies strictly inside the cost range and is strictly smaller on a crowded day, so under state-dependent priority pricing some customers buy fast-track tickets in both states. The ordering makes the two-cutoff solution $(c_r,c_f)=(c(\lambda_h),c(\lambda_l))$ of the AS and AUS programs well ordered.
--
--   **Formalization Note** Stated under the full standing assumptions of the mission (`Params.Standing`); only $0<\lambda_l<\lambda_h<\mu$ and $\bar c>0$ are relevant.
-- source:
--   Wang, Cao, Xie, Zhan, Advance Selling and Upgrading in Priority Queues, MSOM (2025), doi:10.1287/msom.2023.0410, p. 15, §5.1, paragraph after Proposition 3

import Mathlib
import Definitions.Def_AdvSellUpgrade_Online_Setting

namespace AdvSellUpgrade.Online

/-- §5.1, p. 15, paragraph after Proposition 3: under the standing assumptions,
`0 < c(λh) < c(λl) < c̄`. -/
theorem cutoff_order (P : Params) (hP : P.Standing) :
    0 < cFn P.mu P.cbar P.lamH ∧ cFn P.mu P.cbar P.lamH < cFn P.mu P.cbar P.lamL ∧
      cFn P.mu P.cbar P.lamL < P.cbar := by sorry

end AdvSellUpgrade.Online
