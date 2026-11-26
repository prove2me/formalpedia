-- Prove2me | Theorems.Thm_Bsv_StrictSignature_strictSig_injective
-- name    : Bsv.StrictSignature.strictSig_injective
-- status  : Proved
-- author  : @GregoryJWard
-- created : 2026-11-26T11:40:52.933804+00:00
-- url     : https://prove2.me/theorems/c551d8bf-5012-4e79-ae91-34b12042009e
-- title:
--   The strict signature parser is injective on accepted inputs
-- statement:
--   Let `strictSig` be the strict two-integer signature parser of the imported definition. If the byte strings $b_1$ and $b_2$ are both accepted and yield the same pair $(r, s)$, then
--
--   $$
--   b_1 = b_2.
--   $$
--
--   Hence a pair $(r,s)$ has no second accepted encoding. The statement says nothing about whether two different pairs can both be valid signatures of one message.
--
--   **Formalization Note** The statement is about the Lean model of the parser, not about a particular program.
-- source:
--   Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan, BSV Lean proofs (Apache-2.0), theorem strictSig_injective. https://github.com/codenlighten/bsv-lean-proofs

import Definitions.Def_bsv_strict_signature

namespace Bsv.StrictSignature

theorem strictSig_injective (b₁ b₂ r s : List Byte)
    (h₁ : strictSig b₁ = some (r, s)) (h₂ : strictSig b₂ = some (r, s)) :
    b₁ = b₂ := by sorry

end Bsv.StrictSignature
