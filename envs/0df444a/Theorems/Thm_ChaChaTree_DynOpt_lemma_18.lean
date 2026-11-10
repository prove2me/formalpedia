-- Prove2me | Theorems.Thm_ChaChaTree_DynOpt_lemma_18
-- name    : ChaChaTree.DynOpt.lemma_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:23:09.237334+00:00
-- url     : https://prove2.me/theorems/08c920dd-bc88-4fc4-ac84-b018756be430
-- title:
--   Lemma 18 — the depth alternation bound is at most 5·IR(X)
-- statement:
--   Let $[N] = [2^H]$, $T_1$ the perfect binary search tree with the elements of $[N]$ as leaves, and $T_2$ an arbitrary fixed full binary tree with the depths $\{0,\dots,H-1\}$ as leaves. For every access sequence $X$ on $[N]$,
--   $$\mathrm{DepthAlt}_{T_1,T_2}(X) \le 5\,\mathrm{IR}(X),$$
--   where $\mathrm{IR}(X) = \mathrm{IR}(P(X))$.
--
--   Differences from the source:
--   - encoding: T₁ perfect leaf-oriented on [2^H]; T₂ a binary tree with leaves 0, …, H − 1 whose internal nodes have degree 2 → T₁ by depth/position indices (ancIdx, lcaDepth); T₂ : FBT with T₂.numLeaves = H, leaves numbered left to right; reason: same trees; a full binary tree with H leaves numbered in order is exactly such a T₂
--   - encoding: IR(X) → IR (pointsOf X); reason: the paper's IR of a sequence is IR of its instance P(X)
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), Lemma 18, p. 20 (PDF 21); setting §4.4, p. 19 (PDF 20)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_Instance
import Definitions.Def_ChaChaTree_DynOpt_Rectangles
import Definitions.Def_ChaChaTree_DynOpt_RefTrees

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-- **Lemma 18** (p. 20). For `[N] = [2^H]`, the perfect leaf-oriented reference tree `T₁` on
`[N]`, an arbitrary fixed full binary tree `T₂` with leaves `0, …, H − 1`, and every access
sequence `X` on `[N]`: `DepthAlt_{T₁,T₂}(X) ≤ 5 IR(X)`, where `IR(X) = IR(P(X))`. -/
theorem lemma_18 (H : ℕ) (T₂ : FBT) (hT₂ : T₂.numLeaves = H) (X : List ℕ)
    (hX : ∀ x ∈ X, x ∈ Finset.Icc 1 (2 ^ H)) :
    depthAlt H T₂ X ≤ 5 * IR (pointsOf X) := by sorry

end ChaChaTree.DynOpt
