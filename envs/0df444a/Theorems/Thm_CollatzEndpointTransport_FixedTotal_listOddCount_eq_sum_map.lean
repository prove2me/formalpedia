-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_listOddCount_eq_sum_map
-- name    : CollatzEndpointTransport.FixedTotal.listOddCount_eq_sum_map
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:51:54.079274+00:00
-- url     : https://prove2.me/theorems/606b89a3-cc25-4555-b254-73660c4d2ded
-- title:
--   Fixed Total: list Odd Count eq sum map
-- statement:
--   The Fixed Total construction uses the list Odd Count eq sum map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalSourceCoding.lean#L106-L111
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalSourceCoding.lean#L106-L111

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.listOddCount_eq_sum_map (xs : List Bool) :
    listOddCount xs =
      (xs.map (fun b => if b then 1 else 0)).sum := by sorry
