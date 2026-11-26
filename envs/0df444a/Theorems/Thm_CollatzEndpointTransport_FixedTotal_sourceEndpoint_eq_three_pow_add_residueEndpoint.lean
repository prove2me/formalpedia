-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpoint_eq_three_pow_add_residueEndpoint
-- name    : CollatzEndpointTransport.FixedTotal.sourceEndpoint_eq_three_pow_add_residueEndpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:53:17.232294+00:00
-- url     : https://prove2.me/theorems/7982a0b9-b800-4703-80b9-c335b88ccc2f
-- title:
--   Fixed Total: source Endpoint eq three pow add residue Endpoint
-- statement:
--   Exact translation from the canonical residue endpoint to the canonical
--   shell endpoint.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointBridge.lean#L107-L132
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointBridge.lean#L107-L132

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.sourceEndpoint_eq_three_pow_add_residueEndpoint
    {M : ℕ} (x : SourceCode M) :
    sourceEndpoint x =
      3 ^ sourceCodeOddCount x + sourceResidueEndpoint x := by sorry
