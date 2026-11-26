-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_binomialAnnulus_index
-- name    : CollatzEndpointTransport.FixedTotal.mem_binomialAnnulus_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:44:12.864903+00:00
-- url     : https://prove2.me/theorems/605174a0-5746-4bb1-a300-97e55940df91
-- title:
--   Fixed Total: mem binomial Annulus index
-- statement:
--   Every binomial weight belongs to the annulus indexed by integer division
--   of its central distance by the annular width.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L109-L120
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L109-L120

import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 200000

theorem CollatzEndpointTransport.FixedTotal.mem_binomialAnnulus_index
    {H k : ℕ} (hk : k ∈ Finset.range (H + 1)) :
    k ∈ binomialAnnulus H
      (binomialCenterDistance H k / binomialAnnulusWidth H) := by sorry
