-- Prove2me | Theorems.Thm_Bsv_Merkle_rootLit_eq_root
-- name    : Bsv.Merkle.rootLit_eq_root
-- status  : Proved
-- author  : @GregoryJWard
-- created : 2026-11-26T14:29:30.954025+00:00
-- url     : https://prove2.me/theorems/37291d2b-6ca4-5b32-b3b1-de4bc48f82e2
-- title:
--   The array-and-counter Merkle computation returns the root of the tree
-- statement:
--   Let $H$ be an arbitrary binary operation on a type with decidable equality and a default element, and let `rootLit` be the Merkle computation using an array of pending hashes and an unbounded leaf counter, as in the imported definitions. For every list of leaves $l$,
--
--   $$
--   \mathrm{rootLit}_H(l) = \mathrm{root}_H(l).
--   $$
--
--   **Formalization Note** The statement is about the Lean model of the computation, not about a particular program.
-- source:
--   Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan, BSV Lean proofs (Apache-2.0), theorem rootLit_eq_root. https://github.com/codenlighten/bsv-lean-proofs

import Definitions.Def_bsv_merkle_literal

namespace Bsv.Merkle

theorem rootLit_eq_root {α : Type} (H : α → α → α) [DecidableEq α] [Inhabited α] (l : List α) :
    rootLit H l = root H l := by sorry

end Bsv.Merkle
