-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fixedCriticalContribution_le
-- name    : CollatzEndpointTransport.FixedTotal.sum_fixedCriticalContribution_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:57:06.569157+00:00
-- url     : https://prove2.me/theorems/6c6fe0a0-31a5-5b81-8428-5190916ef1b9
-- title:
--   Fixed Total: sum fixed Critical Contribution le
-- statement:
--   The Fixed Total construction uses the sum fixed Critical Contribution le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalGlobalEndpointMoment.lean#L216-L251
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalGlobalEndpointMoment.lean#L216-L251

import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.globalCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.sum_fixedCriticalContribution_le
    (M : ℕ) (u : Fin M) :
    (∑ s ∈ Finset.Icc 1 M,
        fixedCriticalContribution (M - (u : ℕ)) s) ≤
      8 * (M - (u : ℕ)) * (2 ^ (M - (u : ℕ) - 1) : ℝ) := by sorry
