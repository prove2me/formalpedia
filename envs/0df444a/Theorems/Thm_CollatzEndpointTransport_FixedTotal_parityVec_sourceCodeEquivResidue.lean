-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_parityVec_sourceCodeEquivResidue
-- name    : CollatzEndpointTransport.FixedTotal.parityVec_sourceCodeEquivResidue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:51:06.374172+00:00
-- url     : https://prove2.me/theorems/d3c48d54-1b47-5621-a599-dc4f811c3209
-- title:
--   Fixed Total: parity Vec source Code Equiv Residue
-- statement:
--   The Fixed Total construction uses the parity Vec source Code Equiv Residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalSourceCoding.lean#L300-L307
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalSourceCoding.lean#L300-L307

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.parityVec_sourceCodeEquivResidue
    (M : ℕ) (x : SourceCode M) :
    Terras.parityVec M (sourceCodeEquivResidue M x : ℕ) =
      sourceCodeWord x := by sorry
