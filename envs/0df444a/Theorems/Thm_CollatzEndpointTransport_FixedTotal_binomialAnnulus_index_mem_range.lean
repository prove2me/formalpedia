-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomialAnnulus_index_mem_range
-- name    : CollatzEndpointTransport.FixedTotal.binomialAnnulus_index_mem_range
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:44:14.353939+00:00
-- url     : https://prove2.me/theorems/0693815f-c9b0-5225-9093-98f432267dc9
-- title:
--   Fixed Total: binomial Annulus index mem range
-- statement:
--   The Fixed Total construction uses the binomial Annulus index mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L122-L132
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L122-L132

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

theorem CollatzEndpointTransport.FixedTotal.binomialAnnulus_index_mem_range
    {H k : ℕ} (hk : k ∈ Finset.range (H + 1)) :
    binomialCenterDistance H k / binomialAnnulusWidth H ∈
      Finset.range (H + 1) := by sorry
