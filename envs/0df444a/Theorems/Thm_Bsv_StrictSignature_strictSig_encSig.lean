-- Prove2me | Theorems.Thm_Bsv_StrictSignature_strictSig_encSig
-- name    : Bsv.StrictSignature.strictSig_encSig
-- status  : Proved
-- author  : @GregoryJWard
-- created : 2026-11-26T14:26:42.405951+00:00
-- url     : https://prove2.me/theorems/2e3656f9-401f-4ea5-8435-435707f20dfb
-- title:
--   The strict signature parser accepts the encoder's output for all 32-byte values
-- statement:
--   Let `strictSig` be the strict two-integer signature parser and `encSig` the encoder of the imported definition. For all byte strings $r$ and $s$ of length $32$,
--
--   $$
--   \mathrm{strictSig}(\mathrm{encSig}(r, s)) = \mathrm{some}\,(r, s).
--   $$
--
--   So every output of the encoder on 32-byte values is accepted and decodes to the values that were encoded.
--
--   **Formalization Note** The statement is about the Lean model of the computation, not about a particular program.
-- source:
--   Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan. New theorem, not part of the BSV Lean proofs repository. It concerns the parser model defined there: https://github.com/codenlighten/bsv-lean-proofs

import Definitions.Def_bsv_strict_signature

namespace Bsv.StrictSignature

theorem strictSig_encSig (r s : List Byte) (hr : r.length = 32) (hs : s.length = 32) :
    strictSig (encSig r s) = some (r, s) := by sorry

end Bsv.StrictSignature
