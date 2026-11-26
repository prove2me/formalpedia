-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_firstPassagePullback_powerDense
-- name    : FirstPassageLinearTransport.firstPassagePullback_powerDense
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:09:40.533831+00:00
-- url     : https://prove2.me/theorems/2189bdea-b91b-435b-ba0c-fdc519631ead
-- title:
--   First Passage Linear Transport: first Passage Pullback power Dense
-- statement:
--   First-passage pullback preserves quantitative density with
--   linear exponent transport `D ↦ chi D`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L683-L750
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L683-L750

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.firstPassagePullback_powerDense
    {r eta C D chi Dc : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) (hS : PowerDense S C D)
    (hchi0 : 0 < chi) (hchi : chi < r)
    (hDc0 : 0 < Dc)
    (hDDc : D ≤ Dc)
    (hDcRate : chi * Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1) :
    PowerDense (firstPassagePullback p S)
      (pullbackGlobalConstant p chi Dc * (C + 1) * D⁻¹ ^ 2)
      (chi * D) := by sorry
