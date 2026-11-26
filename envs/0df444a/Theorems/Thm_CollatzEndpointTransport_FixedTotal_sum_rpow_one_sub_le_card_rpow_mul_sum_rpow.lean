-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_rpow_one_sub_le_card_rpow_mul_sum_rpow
-- name    : CollatzEndpointTransport.FixedTotal.sum_rpow_one_sub_le_card_rpow_mul_sum_rpow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:50:29.523941+00:00
-- url     : https://prove2.me/theorems/93fd4c98-ae2a-425c-9ab2-736b8b64ac4a
-- title:
--   Fixed Total: sum rpow one sub le card rpow mul sum rpow
-- statement:
--   Finite-set concavity with the total mass retained explicitly.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMassBound.lean#L30-L92
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMassBound.lean#L30-L92

import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 400000

theorem CollatzEndpointTransport.FixedTotal.sum_rpow_one_sub_le_card_rpow_mul_sum_rpow
    {ι : Type*} (U : Finset ι) (p : ι → ℝ)
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hp : ∀ i ∈ U, 0 ≤ p i) :
    ∑ i ∈ U, (p i) ^ (1 - theta) ≤
      (U.card : ℝ) ^ theta * (∑ i ∈ U, p i) ^ (1 - theta) := by sorry
