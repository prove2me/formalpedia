-- Prove2me | Theorems.Thm_Bsv_Merkle_mutatedW_eq
-- name    : Bsv.Merkle.mutatedW_eq
-- status  : Proved
-- author  : @GregoryJWard
-- created : 2026-11-26T14:31:46.762138+00:00
-- url     : https://prove2.me/theorems/8ec45ee5-a39e-4da3-ab6c-949641f23121
-- title:
--   The leaf phase with a W-bit counter computes the duplicate flag below 2^W leaves
-- statement:
--   Let $H$ be an arbitrary binary operation on a type with decidable equality and a default element, and `mutatedW` the flag computed with a $W$-bit counter. If the list $l$ has fewer than $2^W$ leaves, then no fault occurs and
--
--   $$
--   \mathrm{mutatedW}_{H,W}(l) = \mathrm{ok}\big(\mathrm{mutatedTree}_H(l)\big).
--   $$
--
--   `mutatedW` runs the leaf phase only, so this range is larger than that of the root computation: for lists longer than $2^{W-1}$ the root computation on the same list faults.
--
--   **Formalization Note** The statement is about the Lean model of the computation, not about a particular program.
-- source:
--   Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan, BSV Lean proofs (Apache-2.0), theorem mutatedW_eq. https://github.com/codenlighten/bsv-lean-proofs

import Definitions.Def_bsv_merkle_width

namespace Bsv.Merkle

theorem mutatedW_eq {α : Type} (H : α → α → α) [DecidableEq α] [Inhabited α]
    (W : Nat) (l : List α) (hl : l.length < 2 ^ W) :
    mutatedW H W l = .ok (mutatedTree H l) := by sorry

end Bsv.Merkle
