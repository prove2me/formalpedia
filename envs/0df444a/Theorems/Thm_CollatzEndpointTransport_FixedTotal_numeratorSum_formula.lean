-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_numeratorSum_formula
-- name    : CollatzEndpointTransport.FixedTotal.numeratorSum_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:23:23.135431+00:00
-- url     : https://prove2.me/theorems/edd02ad0-36c7-40fc-8b57-51859d80fc71
-- title:
--   Fixed Total: numerator Sum formula
-- statement:
--   The Fixed Total construction uses the numerator Sum formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalFirstMoment.lean#L178-L194
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalFirstMoment.lean#L178-L194

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.numeratorSum_formula
    (N : ℕ) (hN : 0 < N) :
    2 * numeratorSum N = (N + 1) * 4 ^ (N - 1) := by sorry
