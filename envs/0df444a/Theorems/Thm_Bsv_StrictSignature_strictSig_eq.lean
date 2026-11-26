-- Prove2me | Theorems.Thm_Bsv_StrictSignature_strictSig_eq
-- name    : Bsv.StrictSignature.strictSig_eq
-- status  : Proved
-- author  : @GregoryJWard
-- created : 2026-11-26T11:40:17.455424+00:00
-- url     : https://prove2.me/theorems/c5223d04-4b91-4894-8381-6a17a4630944
-- title:
--   Every byte string the parser accepts is the encoder's output for its pair
-- statement:
--   Let `strictSig` be the strict two-integer signature parser and `encSig` the encoder of the imported definition. Let $b$ be a byte string and $r, s$ byte strings. If the parser accepts $b$ and returns $(r, s)$, then
--
--   $$
--   b = \mathrm{encSig}(r, s).
--   $$
--
--   So the parser accepts at most the one encoding of each pair that the encoder produces. The converse (that every output of the encoder is accepted) is not asserted, and nothing is said about whether $r$ or $s$ lies in any particular range.
--
--   **Formalization Note** The statement is about the Lean model of the parser, not about a particular program.
-- source:
--   Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan, BSV Lean proofs (Apache-2.0), theorem strictSig_eq. https://github.com/codenlighten/bsv-lean-proofs

import Definitions.Def_bsv_strict_signature

namespace Bsv.StrictSignature

theorem strictSig_eq (b r s : List Byte) (h : strictSig b = some (r, s)) :
    b = encSig r s := by sorry

end Bsv.StrictSignature
