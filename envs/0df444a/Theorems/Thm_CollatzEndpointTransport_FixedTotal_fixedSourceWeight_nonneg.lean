-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_nonneg
-- name    : CollatzEndpointTransport.FixedTotal.fixedSourceWeight_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:34:43.812709+00:00
-- url     : https://prove2.me/theorems/1b68bc18-5aa0-5117-ae0e-44f70c61135c
-- title:
--   Fixed Total: fixed Source Weight nonneg
-- statement:
--   The Fixed Total construction uses the fixed Source Weight nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1386-L1390
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1386-L1390

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedSourceWeight_nonneg
    (N s : ℕ) :
    0 ≤ fixedSourceWeight N s := by sorry
