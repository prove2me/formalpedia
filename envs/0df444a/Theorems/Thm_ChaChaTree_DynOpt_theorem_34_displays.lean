-- Prove2me | Theorems.Thm_ChaChaTree_DynOpt_theorem_34_displays
-- name    : ChaChaTree.DynOpt.theorem_34_displays
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:23:06.34021+00:00
-- url     : https://prove2.me/theorems/b565a2fb-a5cb-4994-b97d-7624e5417137
-- title:
--   Proof of Theorem 34 — M(X) = m + Flips₁(X) and Flips₁(X) ≤ Alt(X) + (n − 1)
-- statement:
--   Let $n = 2^H \ge 2$ and $T_2$ a full binary tree with leaves $0,\dots,H-1$. For any access sequence $X = (x_1,\dots,x_m)$ to $[n]$, the abstract Cha-cha process satisfies both
--   $$M(X) = m + \mathrm{Flips}_1(X) \qquad\text{and}\qquad \mathrm{Flips}_1(X) \le \mathrm{Alt}(X) + (n-1),$$
--   where $M(X)$ is the number of `ExposeDepth` calls (including the completion call `ExposeDepth(H)` of every access) and $\mathrm{Alt} = \mathrm{Alt}_{T_1}$.
--
--   Differences from the source:
--   - generalization: T₂ a balanced binary search tree with leaves 0, …, H − 1 (§5.2) → any full binary tree T₂ : FBT with T₂.numLeaves = H; reason: the proof never uses balance; balanced T₂ is a special case
--   - encoding: the abstract Cha-cha process of Figure 11 with secondary entries (η, q) → ChaChaState without the fragment identifiers q, and the while loop of Access with a budget of H + 1 iterations; reason: no step reads q, so the counts are unchanged; the loop terminates within H iterations, since each iteration strictly increases depth(lca(z, x)) < H
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), proof of Theorem 34, p. 34 (PDF 35)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_RefTrees
import Definitions.Def_ChaChaTree_DynOpt_ChaChaProcess

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-- **Proof of Theorem 34, two displays** (p. 34). For `n = 2^H ≥ 2`, `T₂` a full binary tree with
leaves `0, …, H − 1` and any access sequence `X = (x₁, …, x_m)` to `[n]`, the abstract Cha-cha
process satisfies `M(X) = m + Flips₁(X)` and `Flips₁(X) ≤ Alt(X) + (n − 1)`. -/
theorem theorem_34_displays (H : ℕ) (hH : 1 ≤ H) (T₂ : FBT) (hT₂ : T₂.numLeaves = H)
    (X : List ℕ) (hX : ∀ x ∈ X, x ∈ Finset.Icc 1 (2 ^ H)) :
    exposeCount H T₂ X = X.length + flips1 H T₂ X ∧
      flips1 H T₂ X ≤ altT1 H X + (2 ^ H - 1) := by sorry

end ChaChaTree.DynOpt
