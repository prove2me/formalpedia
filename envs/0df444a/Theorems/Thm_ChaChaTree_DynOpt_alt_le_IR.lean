-- Prove2me | Theorems.Thm_ChaChaTree_DynOpt_alt_le_IR
-- name    : ChaChaTree.DynOpt.alt_le_IR
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:22:44.715203+00:00
-- url     : https://prove2.me/theorems/2e56fda4-87ed-4872-89b4-c4695814aa4d
-- title:
--   §2.2 — Wilber’s alternation bound is at most IR for arbitrary reference trees
-- statement:
--   For every node-oriented reference BST on $[n]$ (with an access to the vertex itself labeled L as in §2.1), and for every full leaf-oriented ordered reference tree on its ranked leaves (as in §2.2), every access sequence on its keys satisfies $\mathrm{Alt}_{T_1}(X) \le \mathrm{IR}(X)$. The statement also spells out the perfect leaf-oriented specialization in the `altT1` encoding used by later mission items.
--
--   Differences from the source:
--   - encoding: the sum of alternations over the vertices of a reference tree → altBST for the node-oriented convention, altLeaf for the leaf-oriented convention, and the explicit perfect-tree specialization altT1; reason: recursive sums over all subtree separators implement the same label changes; leaves are ranked left to right, and the perfect-tree clause is a specialization of the leaf-oriented clause
--   - encoding: IR(X) → IR (pointsOf X); reason: IR of a sequence is IR of its instance P(X)
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), §2.2, p. 7 (PDF 8), 'Charging Wilber's alternation bound to independent rectangle bounds', argument pp. 7–8

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_Instance
import Definitions.Def_ChaChaTree_DynOpt_Rectangles
import Definitions.Def_ChaChaTree_DynOpt_RefTrees

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-- **§2.2, folklore bound** (pp. 7–8), with the node-oriented convention of §2.1
and the leaf-oriented convention of §2.2: for every reference tree and access sequence
on its keys, `Alt_{T₁}(X) ≤ IR(X)`. The final conjunct spells out the perfect-tree
specialization in the depth/position encoding used by the subsequent items. -/
theorem alt_le_IR :
    (∀ (n : ℕ) (T₁ : BinaryTree ℕ), SplayDynOpt.IsBSTOn n T₁ →
      ∀ X : List ℕ, (∀ x ∈ X, x ∈ Finset.Icc 1 n) →
        altBST T₁ X ≤ IR (pointsOf X)) ∧
    (∀ (T₁ : FBT) (X : List ℕ), (∀ x ∈ X, x ∈ Finset.Icc 1 T₁.numLeaves) →
      altLeaf T₁ 1 X ≤ IR (pointsOf X)) ∧
    (∀ (H : ℕ) (X : List ℕ), (∀ x ∈ X, x ∈ Finset.Icc 1 (2 ^ H)) →
      altT1 H X ≤ IR (pointsOf X)) := by sorry

end ChaChaTree.DynOpt
