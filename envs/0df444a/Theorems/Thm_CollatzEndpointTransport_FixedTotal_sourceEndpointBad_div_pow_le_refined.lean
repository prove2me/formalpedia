-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le_refined
-- name    : CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_refined
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:25:36.041778+00:00
-- url     : https://prove2.me/theorems/6a584d3a-8133-4161-9c63-3a5f3fae345e
-- title:
--   Fixed Total: source Endpoint Bad div pow le refined
-- statement:
--   Full finite-shell estimate before startup and polynomial absorption.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean#L145-L197
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean#L145-L197

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_refined
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
      (((M + 1) * 2 ^ (M - K) : ℕ) : ℝ) / (2 ^ M : ℝ) +
        2 * Real.exp (-2 * (eta / 4) ^ 2 * M) +
        (C * Real.exp (-D * Real.log 3)) ^ holderTargetExponent theta *
          holderCentralMomentConstant theta eta *
          (M + 1 : ℝ) ^ holderScaleExponent theta *
          Real.exp (-centralRenyiRate theta D * M) := by sorry
