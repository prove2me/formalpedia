-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_firstPassagePullback_shell_bound
-- name    : FirstPassageLinearTransport.firstPassagePullback_shell_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:09:34.264376+00:00
-- url     : https://prove2.me/theorems/e2a45e3b-0931-5ac8-8e6c-db8871186a56
-- title:
--   First Passage Linear Transport: first Passage Pullback shell bound
-- statement:
--   Uniform all-shell bound underlying the dense-set pullback theorem.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L522-L679
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L522-L679

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.firstPassagePullback_shell_bound
    {r eta C D chi Dc : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) (hS : PowerDense S C D)
    (hchi0 : 0 < chi) (hchi : chi < r)
    (hDc0 : 0 < Dc)
    (hDDc : D ≤ Dc)
    (hDcRate : chi * Dc ≤ quadraticWindowDensityRate eta)
    (M : ℕ) :
    ((shellBad (firstPassagePullback p S) M).card : ℝ) ≤
      pullbackShellConstant p chi Dc * (C + 1) * D⁻¹ ^ 2 *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by sorry
