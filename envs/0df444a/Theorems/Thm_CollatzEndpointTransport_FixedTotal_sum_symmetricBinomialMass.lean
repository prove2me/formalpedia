-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_symmetricBinomialMass
-- name    : CollatzEndpointTransport.FixedTotal.sum_symmetricBinomialMass
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:44:13.142039+00:00
-- url     : https://prove2.me/theorems/7efeddf2-9ec0-51b3-a122-13f767ad0457
-- title:
--   Fixed Total: sum symmetric Binomial Mass
-- statement:
--   The symmetric binomial masses sum to one.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L170-L178
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L170-L178

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

theorem CollatzEndpointTransport.FixedTotal.sum_symmetricBinomialMass (H : ℕ) :
    ∑ k ∈ Finset.range (H + 1), symmetricBinomialMass H k = 1 := by sorry
