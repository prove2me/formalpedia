-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedCriticalContribution_eq_zero_of_lt_length
-- name    : CollatzEndpointTransport.FixedTotal.fixedCriticalContribution_eq_zero_of_lt_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:57:57.578604+00:00
-- url     : https://prove2.me/theorems/368bb6c7-29d0-4af7-8c39-d4a7816562fd
-- title:
--   Fixed Total: fixed Critical Contribution eq zero of lt length
-- statement:
--   The Fixed Total construction uses the fixed Critical Contribution eq zero of lt length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalGlobalEndpointMoment.lean#L204-L214
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalGlobalEndpointMoment.lean#L204-L214

import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.globalCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.fixedCriticalContribution_eq_zero_of_lt_length
    {N s : ℕ} (h : N < s) :
    fixedCriticalContribution N s = 0 := by sorry
