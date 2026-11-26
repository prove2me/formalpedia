-- Prove2me | Theorems.Thm_Bsv_Merkle_branch_zero_indep
-- name    : Bsv.Merkle.branch_zero_indep
-- status  : Proved
-- author  : @GregoryJWard
-- created : 2026-11-26T11:41:24.714808+00:00
-- url     : https://prove2.me/theorems/a4b15dce-58dc-489a-9a2a-06df0ab0a643
-- title:
--   The Merkle branch of the first leaf does not depend on that leaf
-- statement:
--   Let $H$ be an arbitrary binary operation, and let `branch` be the Merkle branch of the imported definition. For all nodes $x, y$ and every list $t$,
--
--   $$
--   \mathrm{branch}_H(x :: t,\ 0) = \mathrm{branch}_H(y :: t,\ 0).
--   $$
--
--   So the branch of position $0$ can be computed before the first leaf is known. The statement concerns position $0$ only, and says nothing about the root.
--
--   **Formalization Note** The statement is about the Lean model of the tree, not about a particular program.
-- source:
--   Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan, BSV Lean proofs (Apache-2.0), theorem branch_zero_indep. https://github.com/codenlighten/bsv-lean-proofs/blob/41c4bfdc5ce4dd9bfbf0e21c77e6586d041261de/BsvLeanProofs/Merkle.lean

import Definitions.Def_bsv_merkle_tree

namespace Bsv.Merkle

theorem branch_zero_indep {α : Type} (H : α → α → α) (x y : α) (t : List α) :
    branch H (x :: t) 0 = branch H (y :: t) 0 := by sorry

end Bsv.Merkle
