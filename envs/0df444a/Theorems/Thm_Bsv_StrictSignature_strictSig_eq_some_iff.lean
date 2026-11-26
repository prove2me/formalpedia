-- Prove2me | Theorems.Thm_Bsv_StrictSignature_strictSig_eq_some_iff
-- name    : Bsv.StrictSignature.strictSig_eq_some_iff
-- status  : Proved
-- author  : @GregoryJWard
-- created : 2026-11-26T14:27:09.08027+00:00
-- url     : https://prove2.me/theorems/a7319387-7d4c-5004-9893-a396548b3175
-- title:
--   Complete description of the inputs the strict signature parser accepts
-- statement:
--   Let `strictSig` and `encSig` be the parser and encoder of the imported definition. For all byte strings $b, r, s$,
--
--   $$
--   \mathrm{strictSig}(b) = \mathrm{some}\,(r, s) \iff |r| = 32,\; |s| = 32 \text{ and } b = \mathrm{encSig}(r, s).
--   $$
--
--   Hence the accepted inputs are exactly the encodings of pairs of 32-byte values, each pair having exactly one.
--
--   **Formalization Note** The statement is about the Lean model of the computation, not about a particular program.
-- source:
--   Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan. New theorem, not part of the BSV Lean proofs repository. It concerns the parser model defined there: https://github.com/codenlighten/bsv-lean-proofs

import Definitions.Def_bsv_strict_signature

namespace Bsv.StrictSignature

theorem strictSig_eq_some_iff (b r s : List Byte) :
    strictSig b = some (r, s) ↔ r.length = 32 ∧ s.length = 32 ∧ b = encSig r s := by sorry

end Bsv.StrictSignature
