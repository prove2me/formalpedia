-- Prove2me | Theorems.Thm_Bsv_Merkle_rootW_ok_iff
-- name    : Bsv.Merkle.rootW_ok_iff
-- status  : Proved
-- author  : @GregoryJWard
-- created : 2026-11-26T14:32:26.13437+00:00
-- url     : https://prove2.me/theorems/a6eafc06-27ca-554c-8445-66ee363bb792
-- title:
--   A W-bit Merkle root computation succeeds exactly up to 2^(W-1) leaves
-- statement:
--   Let $H$ be an arbitrary binary operation on a type with decidable equality and a default element, $W \ge 1$, and `rootW` the array-and-counter Merkle computation with a $W$-bit counter. For every list of leaves $l$, the computation returns a value, rather than a fault, if and only if
--
--   $$
--   |l| \le 2^{W-1}.
--   $$
--
--   The bound is therefore exact. For $W = 32$ it is $2^{31}$ leaves.
--
--   **Formalization Note** The statement is about the Lean model of the computation, not about a particular program.
-- source:
--   Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan, BSV Lean proofs (Apache-2.0), theorem rootW_ok_iff. https://github.com/codenlighten/bsv-lean-proofs

import Definitions.Def_bsv_merkle_width

namespace Bsv.Merkle

theorem rootW_ok_iff {α : Type} (H : α → α → α) [DecidableEq α] [Inhabited α]
    (W : Nat) (hW : 0 < W) (l : List α) :
    (∃ r, rootW H W l = .ok r) ↔ l.length ≤ 2 ^ (W - 1) := by sorry

end Bsv.Merkle
