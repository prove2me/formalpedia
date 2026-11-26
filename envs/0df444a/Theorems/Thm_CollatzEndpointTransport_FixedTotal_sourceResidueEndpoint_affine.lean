-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceResidueEndpoint_affine
-- name    : CollatzEndpointTransport.FixedTotal.sourceResidueEndpoint_affine
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:53:03.302004+00:00
-- url     : https://prove2.me/theorems/54111b26-c69b-52ff-aa49-7031420d42de
-- title:
--   Fixed Total: source Residue Endpoint affine
-- statement:
--   The Fixed Total construction uses the source Residue Endpoint affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointBridge.lean#L94-L103
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointBridge.lean#L94-L103

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.sourceResidueEndpoint_affine
    {M : ℕ} (x : SourceCode M) :
    2 ^ M * sourceResidueEndpoint x =
      3 ^ sourceCodeOddCount x * (sourceCodeEquivResidue M x : ℕ) +
        sourceCodeCorrection x := by sorry
