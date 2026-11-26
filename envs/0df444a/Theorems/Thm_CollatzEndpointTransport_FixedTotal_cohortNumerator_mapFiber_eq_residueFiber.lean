-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortNumerator_mapFiber_eq_residueFiber
-- name    : CollatzEndpointTransport.FixedTotal.cohortNumerator_mapFiber_eq_residueFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:54:02.104727+00:00
-- url     : https://prove2.me/theorems/d0066618-f55d-42f6-9dd2-a3de6f6b6586
-- title:
--   Fixed Total: cohort Numerator map Fiber eq residue Fiber
-- statement:
--   The Fixed Total construction uses the cohort Numerator map Fiber eq residue Fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointMoment.lean#L166-L172
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointMoment.lean#L166-L172

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.endpointCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.cohortNumerator_mapFiber_eq_residueFiber
    {N s : ℕ} (a : Fin (3 ^ s)) :
    mapFiber (fixedSet N s)
        (cohortNumeratorResidue (s := s)) a =
      residueFiber (fixedSet N s) syracuseNumerator (3 ^ s) a := by sorry
