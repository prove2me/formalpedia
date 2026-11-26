-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedCriticalContribution_le
-- name    : CollatzEndpointTransport.FixedTotal.fixedCriticalContribution_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:24:13.48083+00:00
-- url     : https://prove2.me/theorems/9bfa386c-eb44-5652-857c-4c5055235d55
-- title:
--   Fixed Total: fixed Critical Contribution le
-- statement:
--   The Fixed Total construction uses the fixed Critical Contribution le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCriticalMoment.lean#L115-L145
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCriticalMoment.lean#L115-L145

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.compositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.fixedCriticalContribution_le
    (N s : ℕ) :
    fixedCriticalContribution N s ≤
      4 * Real.sqrt
        (∑ c ∈ fixedSet N s, (3 ^ s + syracuseNumerator c)) := by sorry
