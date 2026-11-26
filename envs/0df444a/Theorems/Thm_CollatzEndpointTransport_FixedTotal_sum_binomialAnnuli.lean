-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_binomialAnnuli
-- name    : CollatzEndpointTransport.FixedTotal.sum_binomialAnnuli
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:49:53.81957+00:00
-- url     : https://prove2.me/theorems/86aa64b1-0a8e-4e74-9ee4-7e98b190b277
-- title:
--   Fixed Total: sum binomial Annuli
-- statement:
--   The annuli partition the complete binomial support.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L135-L167
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L135-L167

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

theorem CollatzEndpointTransport.FixedTotal.sum_binomialAnnuli
    {H : ℕ} (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range (H + 1), f k) =
      ∑ j ∈ Finset.range (H + 1), ∑ k ∈ binomialAnnulus H j, f k := by sorry
