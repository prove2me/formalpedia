-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_tendsto_exp_log_sq_sub_rpow
-- name    : FirstPassageLinearTransport.tendsto_exp_log_sq_sub_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:35:42.125105+00:00
-- url     : https://prove2.me/theorems/9ab83b3f-e38c-475d-857e-aa357dc2a512
-- title:
--   First Passage Linear Transport: tendsto exp log sq sub rpow
-- statement:
--   A quadratic logarithmic prefactor is swallowed by every positive power
--   in a negative exponential.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Scalar.lean#L21-L65
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Scalar.lean#L21-L65

import Definitions.Def_FirstPassageLinearTransport_Bootstrap
import Definitions.Def_FirstPassageLinearTransport_Scalar
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter Asymptotics
noncomputable section

theorem FirstPassageLinearTransport.tendsto_exp_log_sq_sub_rpow
    {A c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    Tendsto (fun x : ℝ =>
      Real.exp (A * (Real.log x) ^ 2 - c * x ^ s))
      atTop (nhds 0) := by sorry
