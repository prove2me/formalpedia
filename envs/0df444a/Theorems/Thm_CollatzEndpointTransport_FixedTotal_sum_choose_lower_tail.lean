-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_choose_lower_tail
-- name    : CollatzEndpointTransport.FixedTotal.sum_choose_lower_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:43:57.028671+00:00
-- url     : https://prove2.me/theorems/e6335a5b-8512-59ac-a5fd-147a8e517e69
-- title:
--   Fixed Total: sum choose lower tail
-- statement:
--   The Fixed Total construction uses the sum choose lower tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L180-L184
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L180-L184

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

theorem CollatzEndpointTransport.FixedTotal.sum_choose_lower_tail (H K : ℕ) :
    (∑ k ∈ Finset.Ico 0 (K + 1), (H.choose k : ℝ)) =
      CollatzEndpointTransport.Terras.lowerBinomialSum H K := by sorry
