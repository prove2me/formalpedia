-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_increaseFirst
-- name    : CollatzEndpointTransport.FixedTotal.syracuseNumerator_increaseFirst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:59.803751+00:00
-- url     : https://prove2.me/theorems/92bd9f48-73ee-5b3d-aca2-821b3e58ee36
-- title:
--   Fixed Total: syracuse Numerator increase First
-- statement:
--   The Fixed Total construction uses the syracuse Numerator increase First property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCompositionRecurrence.lean#L217-L231
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCompositionRecurrence.lean#L217-L231

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.syracuseNumerator_increaseFirst
    {N : ℕ} (hN : 0 < N) (c : Composition N) :
    syracuseNumerator (increaseFirst hN c) + 3 ^ (c.length - 1) =
      2 * syracuseNumerator c := by sorry
