-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_bad_bound
-- name    : CollatzEndpointTransport.QuantitativeDensity.IsCDDense.bad_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:07:19.761486+00:00
-- url     : https://prove2.me/theorems/59e3dee3-902f-5e29-82e7-6f6f0aadbeb9
-- title:
--   Is CDDense: bad bound
-- statement:
--   The Is CDDense construction uses the bad bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensity.lean#L61-L64
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensity.lean#L61-L64

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensity
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.QuantitativeDensity.IsCDDense.bad_bound
    {S : Set ℕ} {C D : ℝ} (h : IsCDDense S C D) (N : ℕ) (hN : 0 < N) :
    ((badPrefix S N).card : ℝ) ≤ C * (N : ℝ) ^ (1 - D) := by sorry
