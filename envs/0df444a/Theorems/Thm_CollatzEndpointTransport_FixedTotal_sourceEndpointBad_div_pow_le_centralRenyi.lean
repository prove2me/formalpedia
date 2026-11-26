-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le_centralRenyi
-- name    : CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_centralRenyi
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:18:13.397545+00:00
-- url     : https://prove2.me/theorems/99131cd8-1019-50a2-a10d-4ad23a68f820
-- title:
--   Fixed Total: source Endpoint Bad div pow le central Renyi
-- statement:
--   Full finite-shell theorem, including the explicit noncentral discard.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1144-L1205
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1144-L1205

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

theorem CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_centralRenyi
    {S : Set ℕ} {C D theta eta : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (M K : ℕ) (hKM : K ≤ M)
    (hK : (K : ℝ) ≤ eta * M / 8)
    (hetaM : 4 ≤ eta * M)
    (hstartup : ∀ N : ℕ, M - K ≤ N → N ≤ M →
      1 < N ∧
      (1 / 2 - eta) * N > 1 / 2 ∧
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1) ∧
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      (((M + 1) * 2 ^ (M - K) : ℕ) : ℝ) /
          (2 ^ M : ℝ) +
        2 * Real.exp (-2 * (eta / 4) ^ 2 * M) +
        (C * Real.exp (-D * Real.log 3) +
            (3 : ℝ) ^ theta * centralMomentConstant theta eta *
              (M + 1 : ℝ) ^ 6) *
          Real.exp (-centralRenyiRate theta D * M) := by sorry
