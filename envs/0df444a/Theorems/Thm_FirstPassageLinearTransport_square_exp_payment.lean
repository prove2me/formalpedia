-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_square_exp_payment
-- name    : FirstPassageLinearTransport.square_exp_payment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:09:14.209236+00:00
-- url     : https://prove2.me/theorems/5eb59e8b-d5fb-5a38-ba41-abd83cfc3f5f
-- title:
--   First Passage Linear Transport: square exp payment
-- statement:
--   Elementary polynomial-versus-exponential payment used in (5.14).
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L287-L314
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L287-L314

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.square_exp_payment {q x : ℝ} (hq : 0 < q) (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-(q * x)) ≤ 4 / q ^ 2 := by sorry
