-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_actualCriticalEndpointInformation_le
-- name    : CollatzEndpointTransport.FixedTotal.actualCriticalEndpointInformation_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:00:23.529981+00:00
-- url     : https://prove2.me/theorems/7ee8a056-8e94-5fba-a220-1919caaef656
-- title:
--   Fixed Total: actual Critical Endpoint Information le
-- statement:
--   The Fixed Total construction uses the actual Critical Endpoint Information le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalActualEndpointMoment.lean#L209-L214
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalActualEndpointMoment.lean#L209-L214

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalOddCountMGF
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.actualCriticalEndpointInformation_le
    (M : ℕ) (hM : 1 ≤ M) :
    actualCriticalEndpointInformation M ≤
      9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M := by sorry
