-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_choose_upper_tail
-- name    : CollatzEndpointTransport.FixedTotal.sum_choose_upper_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:44:37.674064+00:00
-- url     : https://prove2.me/theorems/f3fa3f44-f739-5501-90c1-c80fd097fcc9
-- title:
--   Fixed Total: sum choose upper tail
-- statement:
--   The Fixed Total construction uses the sum choose upper tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L186-L206
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L186-L206

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

theorem CollatzEndpointTransport.FixedTotal.sum_choose_upper_tail
    {H K : ℕ} (hKH : K ≤ H) :
    (∑ k ∈ Finset.Ico (H - K) (H + 1), (H.choose k : ℝ)) =
      CollatzEndpointTransport.Terras.lowerBinomialSum H K := by sorry
