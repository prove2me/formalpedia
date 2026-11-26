-- Prove2me | Theorems.Thm_Bsv_Merkle_rootW_eq
-- name    : Bsv.Merkle.rootW_eq
-- status  : Proved
-- author  : @GregoryJWard
-- created : 2026-11-26T14:30:57.360207+00:00
-- url     : https://prove2.me/theorems/12419484-9815-556b-aef8-e7da66f74b97
-- title:
--   A W-bit Merkle counter is correct for up to 2^(W-1) leaves
-- statement:
--   Let $H$ be an arbitrary binary operation on a type with decidable equality and a default element, and `rootW` the array-and-counter Merkle computation with a $W$-bit counter, as in the imported definitions. If $W \ge 1$ and the list $l$ has at most $2^{W-1}$ leaves, then no fault occurs and
--
--   $$
--   \mathrm{rootW}_{H,W}(l) = \mathrm{ok}\big(\mathrm{root}_H(l)\big).
--   $$
--
--   For $W = 32$ the bound is $2^{31}$ leaves.
--
--   **Formalization Note** The statement is about the Lean model of the computation, not about a particular program.
-- source:
--   Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan, BSV Lean proofs (Apache-2.0), theorem rootW_eq. https://github.com/codenlighten/bsv-lean-proofs

import Definitions.Def_bsv_merkle_width

namespace Bsv.Merkle

theorem rootW_eq {α : Type} (H : α → α → α) [DecidableEq α] [Inhabited α]
    (W : Nat) (hW : 0 < W) (l : List α) (hl : l.length ≤ 2 ^ (W - 1)) :
    rootW H W l = .ok (root H l) := by sorry

end Bsv.Merkle
