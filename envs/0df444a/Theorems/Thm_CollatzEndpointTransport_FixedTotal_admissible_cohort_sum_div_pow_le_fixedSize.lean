-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_admissible_cohort_sum_div_pow_le_fixedSize
-- name    : CollatzEndpointTransport.FixedTotal.admissible_cohort_sum_div_pow_le_fixedSize
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:23:26.688056+00:00
-- url     : https://prove2.me/theorems/53bb2065-993c-51ee-96b1-8c63ad45fb6b
-- title:
--   Fixed Total: admissible cohort sum div pow le fixed Size
-- statement:
--   One first-odd cohort after dyadic normalization and the refined aggregate.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralEndpointInformation.lean#L107-L163
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralEndpointInformation.lean#L107-L163

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

theorem CollatzEndpointTransport.FixedTotal.admissible_cohort_sum_div_pow_le_fixedSize
    {M : ℕ} (u : Fin M) {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    (∑ s ∈ shellAdmissibleLengthSet M (M - (u : ℕ)) theta eta,
        ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
          fixedRenyiMoment (M - (u : ℕ)) s theta) /
        (2 : ℝ) ^ M ≤
      ((2 : ℝ) ^ (u : ℕ))⁻¹ *
        ((fixedSizeCentralMomentConstant theta eta *
            fractionalBinomialMassConstant theta) *
          (M + 1 : ℝ) ^ (theta / 2)) := by sorry
