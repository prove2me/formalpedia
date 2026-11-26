-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomialAnnulus_tails_disjoint
-- name    : CollatzEndpointTransport.FixedTotal.binomialAnnulus_tails_disjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:44:32.364231+00:00
-- url     : https://prove2.me/theorems/4740860d-545d-5cd3-b15a-f847c4081382
-- title:
--   Fixed Total: binomial Annulus tails disjoint
-- statement:
--   The Fixed Total construction uses the binomial Annulus tails disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L256-L288
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L256-L288

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

theorem CollatzEndpointTransport.FixedTotal.binomialAnnulus_tails_disjoint
    {H j : ℕ} (hH : 0 < H) (hj : 0 < j) :
    Disjoint
      (Finset.Ico 0 (binomialAnnulusCutoff H j + 1))
      (Finset.Ico (H - binomialAnnulusCutoff H j) (H + 1)) := by sorry
