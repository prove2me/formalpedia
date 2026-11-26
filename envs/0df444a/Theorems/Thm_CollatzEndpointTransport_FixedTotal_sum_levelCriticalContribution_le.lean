-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_levelCriticalContribution_le
-- name    : CollatzEndpointTransport.FixedTotal.sum_levelCriticalContribution_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:58:24.150825+00:00
-- url     : https://prove2.me/theorems/63311b6e-a1b6-4cf0-9138-f0448288c26b
-- title:
--   Fixed Total: sum level Critical Contribution le
-- statement:
--   The Fixed Total construction uses the sum level Critical Contribution le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalGlobalEndpointMoment.lean#L259-L304
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalGlobalEndpointMoment.lean#L259-L304

import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.globalCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.sum_levelCriticalContribution_le
    (M : ℕ) :
    (∑ s ∈ Finset.Icc 1 M, levelCriticalContribution M s) ≤
      Real.sqrt M * (8 * M * (2 ^ M : ℝ)) := by sorry
