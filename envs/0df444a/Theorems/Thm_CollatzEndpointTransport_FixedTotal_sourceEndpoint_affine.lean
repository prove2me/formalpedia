-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpoint_affine
-- name    : CollatzEndpointTransport.FixedTotal.sourceEndpoint_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:52:37.55828+00:00
-- url     : https://prove2.me/theorems/122a1226-3a0c-5a83-b1d5-691ab8ef4e8e
-- title:
--   Fixed Total: source Endpoint affine
-- statement:
--   Exact integer affine formula for a source code in the dyadic shell.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointBridge.lean#L85-L92
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointBridge.lean#L85-L92

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.sourceEndpoint_affine
    {M : ℕ} (x : SourceCode M) :
    2 ^ M * sourceEndpoint x =
      3 ^ sourceCodeOddCount x * sourceShellStart x +
        sourceCodeCorrection x := by sorry
