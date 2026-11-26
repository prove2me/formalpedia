-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_levelCriticalContribution_le
-- name    : CollatzEndpointTransport.FixedTotal.levelCriticalContribution_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:56:37.654591+00:00
-- url     : https://prove2.me/theorems/2af38350-ef54-5f7e-b40c-c6a1c0cbdca2
-- title:
--   Fixed Total: level Critical Contribution le
-- statement:
--   The Fixed Total construction uses the level Critical Contribution le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalGlobalEndpointMoment.lean#L121-L202
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalGlobalEndpointMoment.lean#L121-L202

import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.globalCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.levelCriticalContribution_le
    (M s : ℕ) :
    levelCriticalContribution M s ≤
      Real.sqrt M *
        ∑ u : Fin M,
          fixedCriticalContribution (M - (u : ℕ)) s := by sorry
