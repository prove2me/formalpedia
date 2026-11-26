-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_shell_admissible_fixed_total_aggregate_le_fixedSize
-- name    : CollatzEndpointTransport.FixedTotal.shell_admissible_fixed_total_aggregate_le_fixedSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:23:47.665047+00:00
-- url     : https://prove2.me/theorems/41d40e4b-803a-4c11-ba6d-5858a747e379
-- title:
--   Fixed Total: shell admissible fixed total aggregate le fixed Size
-- statement:
--   The shell-admissible fixed-total levels inherit the refined aggregate.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralEndpointInformation.lean#L29-L104
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralEndpointInformation.lean#L29-L104

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralAggregate
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralEndpointInformation
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 600000

theorem CollatzEndpointTransport.FixedTotal.shell_admissible_fixed_total_aggregate_le_fixedSize
    {M N : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (hN : 0 < N) :
    (∑ s ∈ shellAdmissibleLengthSet M N theta eta,
        fixedSourceWeight N s * fixedRenyiMoment N s theta) ≤
      (fixedSizeCentralMomentConstant theta eta *
          fractionalBinomialMassConstant theta) *
        (N : ℝ) ^ (theta / 2) := by sorry
