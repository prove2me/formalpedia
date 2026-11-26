-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_shellBad_collatzPullback_le_centralRenyi
-- name    : CollatzEndpointTransport.FixedTotal.shellBad_collatzPullback_le_centralRenyi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:18:52.587337+00:00
-- url     : https://prove2.me/theorems/968d0914-c96e-58a9-a4cc-0474def15dfb
-- title:
--   Fixed Total: shell Bad collatz Pullback le central Renyi
-- statement:
--   The Fixed Total construction uses the shell Bad collatz Pullback le central Renyi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1553-L1574
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1553-L1574

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq

theorem CollatzEndpointTransport.FixedTotal.shellBad_collatzPullback_le_centralRenyi
    {S : Set ℕ} {C D theta eta transport : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hcutLate : centralRenyiShellRate theta transport D ≤
      eta * Real.log 2 / 16)
    (hcutParity : centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8)
    (M : ℕ) :
    ((QuantitativeDensity.shellBad
        (QuantitativeDensity.collatzPullback S) M).card : ℝ) ≤
      centralRenyiShellConstant C theta eta transport D *
        Real.exp (-centralRenyiShellRate theta transport D * M) *
        (2 ^ M : ℝ) := by sorry
