-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_child_numerator_sum
-- name    : CollatzEndpointTransport.FixedTotal.child_numerator_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:23:24.267889+00:00
-- url     : https://prove2.me/theorems/336c05a5-df5d-4179-8624-8bb8e43dc76a
-- title:
--   Fixed Total: child numerator sum
-- statement:
--   The Fixed Total construction uses the child numerator sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalFirstMoment.lean#L136-L148
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalFirstMoment.lean#L136-L148

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.child_numerator_sum
    {N : ℕ} (hN : 0 < N) (c : Composition N) :
    syracuseNumerator (increaseFirst hN c) +
        syracuseNumerator (prependOne c) =
      4 * syracuseNumerator c + 2 * 3 ^ (c.length - 1) := by sorry
