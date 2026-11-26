-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_weight_mul_rpow_mul_rpow_le
-- name    : CollatzEndpointTransport.FixedTotal.sum_weight_mul_rpow_mul_rpow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:23:52.648976+00:00
-- url     : https://prove2.me/theorems/415d8b11-38cd-4a89-869d-b68c847d98a5
-- title:
--   Fixed Total: sum weight mul rpow mul rpow le
-- statement:
--   Weighted finite Holder in the exponent coordinates used by the endpoint
--   transport argument.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralRenyiTransport.lean#L29-L122
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralRenyiTransport.lean#L29-L122

import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Mathlib.Analysis.MeanInequalities
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiTransport
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.sum_weight_mul_rpow_mul_rpow_le
    {ι : Type*} (U : Finset ι) (w a b : ι → ℝ)
    {theta : ℝ} (htheta : 0 < theta)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∑ i ∈ U,
        w i * (a i) ^ (theta / (1 + theta)) *
          (b i) ^ (1 / (1 + theta)) ≤
      (∑ i ∈ U, w i * a i) ^ (theta / (1 + theta)) *
        (∑ i ∈ U, w i * b i) ^ (1 / (1 + theta)) := by sorry
