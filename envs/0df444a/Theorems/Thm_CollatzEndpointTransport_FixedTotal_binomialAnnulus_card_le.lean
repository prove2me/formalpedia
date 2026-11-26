-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomialAnnulus_card_le
-- name    : CollatzEndpointTransport.FixedTotal.binomialAnnulus_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:49:43.754058+00:00
-- url     : https://prove2.me/theorems/68432144-4872-5051-acc3-7d7eb6c7284c
-- title:
--   Fixed Total: binomial Annulus card le
-- statement:
--   The Fixed Total construction uses the binomial Annulus card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L76-L105
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L76-L105

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

theorem CollatzEndpointTransport.FixedTotal.binomialAnnulus_card_le (H j : ℕ) :
    (binomialAnnulus H j).card ≤ 2 * binomialAnnulusWidth H := by sorry
