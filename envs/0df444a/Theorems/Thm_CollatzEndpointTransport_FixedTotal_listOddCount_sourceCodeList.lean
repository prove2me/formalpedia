-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_listOddCount_sourceCodeList
-- name    : CollatzEndpointTransport.FixedTotal.listOddCount_sourceCodeList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:51:46.045429+00:00
-- url     : https://prove2.me/theorems/4a99489e-b1e0-4c49-a8d2-b3d5c1f8211c
-- title:
--   Fixed Total: list Odd Count source Code List
-- statement:
--   The Fixed Total construction uses the list Odd Count source Code List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalSourceCoding.lean#L161-L168
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalSourceCoding.lean#L161-L168

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.listOddCount_sourceCodeList
    {M : ℕ} (x : SourceCode M) :
    listOddCount (sourceCodeList x) = sourceCodeOddCount x := by sorry
