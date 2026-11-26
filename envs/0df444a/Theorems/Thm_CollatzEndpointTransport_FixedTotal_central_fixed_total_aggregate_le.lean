-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_central_fixed_total_aggregate_le
-- name    : CollatzEndpointTransport.FixedTotal.central_fixed_total_aggregate_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:46:08.834158+00:00
-- url     : https://prove2.me/theorems/88d6e54a-c800-59cf-b2ac-6349a83611fa
-- title:
--   Fixed Total: central fixed total aggregate le
-- statement:
--   Coarse aggregate central moment.  Its quadratic polynomial prefactor
--   is sufficient for the endpoint-only theorem.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1545-L1596
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1545-L1596

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.central_fixed_total_aggregate_le
    {N : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (hN : 3 < N)
    (hsizePi :
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1))
    (hsizeDrift :
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N)
    (hinterior :
      ∀ s ∈ centralLengthSet N eta, 1 < s ∧ s < N) :
    (∑ s ∈ centralLengthSet N eta,
        fixedSourceWeight N s * fixedRenyiMoment N s theta) ≤
      centralMomentConstant theta eta * (N + 1) ^ 2 := by sorry
