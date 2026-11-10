-- Prove2me | Theorems.Thm_ChaChaTree_DynOpt_lemma_27
-- name    : ChaChaTree.DynOpt.lemma_27
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:23:05.549837+00:00
-- url     : https://prove2.me/theorems/77e4c306-e1bc-40dc-a4e0-d343a7bf5b97
-- title:
--   Lemma 27 — secondary flips: Flips₂ ≤ 2·DepthAlt + 2·Alt + 5n + 2m
-- statement:
--   Let $n = 2^H \ge 2$, $T_1$ the perfect leaf-oriented tree on $[n]$ and $T_2$ a full binary tree with leaves $0,\dots,H-1$. For any access sequence $X = (x_1,\dots,x_m)$ to $[n]$, the number of secondary flips of the abstract Cha-cha process (Figure 11) satisfies
--   $$\mathrm{Flips}_2 \le 2\,\mathrm{DepthAlt}_{T_1,T_2}(X) + 2\,\mathrm{Alt}_{T_1}(X) + 5n + 2m.$$
--
--   Differences from the source:
--   - generalization: T₂ a balanced binary search tree with leaves 0, …, H − 1 (§5.2) → any full binary tree T₂ : FBT with T₂.numLeaves = H; reason: the proof never uses balance; balanced T₂ is a special case
--   - encoding: the abstract Cha-cha process of Figure 11 with secondary entries (η, q) → ChaChaState without the fragment identifiers q, and the while loop of Access with a budget of H + 1 iterations; reason: no step reads q, so the counts are unchanged; the loop terminates within H iterations, since each iteration strictly increases depth(lca(z, x)) < H
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), Lemma 27, p. 28 (PDF 29)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_RefTrees
import Definitions.Def_ChaChaTree_DynOpt_ChaChaProcess

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-- **Lemma 27** (p. 28). Let `n = 2^H ≥ 2`, `T₁` the perfect leaf-oriented tree on `[n]` and `T₂`
a full binary tree with leaves `0, …, H − 1`. For any access sequence `X = (x₁, …, x_m)` to `[n]`,
the secondary flips of the abstract Cha-cha process satisfy
`Flips₂ ≤ 2 DepthAlt_{T₁,T₂}(X) + 2 Alt_{T₁}(X) + 5n + 2m`. -/
theorem lemma_27 (H : ℕ) (hH : 1 ≤ H) (T₂ : FBT) (hT₂ : T₂.numLeaves = H) (X : List ℕ)
    (hX : ∀ x ∈ X, x ∈ Finset.Icc 1 (2 ^ H)) :
    flips2 H T₂ X ≤ 2 * depthAlt H T₂ X + 2 * altT1 H X + 5 * 2 ^ H + 2 * X.length := by sorry

end ChaChaTree.DynOpt
