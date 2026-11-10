-- Prove2me | Theorems.Thm_ChaChaTree_DynOpt_theorem_36
-- name    : ChaChaTree.DynOpt.theorem_36
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:23:02.267596+00:00
-- url     : https://prove2.me/theorems/993d3926-904a-4f10-abc3-ac8b296ad47f
-- title:
--   Theorem 36 (consequence clause) — an online BST realization costs O((n + M(X) + Flips₂(X))·λ)
-- statement:
--   There is a constant $C$ such that for every $n = 2^H \ge 2$ and every full binary tree $T_2$ with leaves $0,\dots,H-1$ (with $B$ the tree with left subtree $T_2$ and right leaf $H$, $K = \mathrm{height}(B)$ and $\lambda = 1 + \log(K+1)$), some deterministic online BST algorithm on exactly the keys $[n]$, in the standard BST model of §5.1, serves every access sequence $X$ on $[n]$ with total cost, initialization included,
--   $$\mathrm{cost}(X) \le C\,\big(n + M(X) + \mathrm{Flips}_2(X)\big)\,\lambda,$$
--   where $M$ and $\mathrm{Flips}_2$ are the counts of the abstract Cha-cha process with reference trees $T_1$, $T_2$.
--
--   This item is the quantitative "Consequently" clause of Theorem 36. Its guarantees 1–3 (amortized costs of `AccessExit` and `SwitchHead`, initialization in $O(n\lambda)$ operations) and the per-vertex storage bound are properties of the named realizations and are not separate items.
--
--   Differences from the source:
--   - reading: both the Cha-Cha-Balanced and the Cha-Cha-Splay tree realize the interface and serve X in O((n + M(X) + Flips₂(X))λ) → ∃ C, ∀ H ≥ 1, ∀ T₂, ∃ A : OnlineBSTAlg (2^H) serving every X with cost ≤ C·(n + M(X) + Flips₂(X))·λ; reason: the two realizations (App. A) are assembled from cited simulations ([MPWZ19]; [DILÖ13, Thm 7]) and are not specified to the level of a Lean definition; the clause asserts the existence of an online deterministic BST with this cost, with C uniform
--   - reading: guarantees 1–3 and O(log(n + 1)) bits of extra state per vertex → not stated (the item is the 'Consequently' clause); reason: the selected source target is explicitly the quantitative consequence clause, as marked in the title; the separate interface and storage guarantees are outside that selected clause
--   - generalization: T₂ a balanced binary search tree with leaves 0, …, H − 1 (§5.2) → any full binary tree T₂ : FBT with T₂.numLeaves = H; reason: the proof never uses balance; balanced T₂ is a special case
--   - encoding: λ = 1 + log(K + 1) → 1 + logb 2 (K + 1) with K = (refB T₂).height; reason: the paper's log is base 2; K + 1 ≥ 2, so no clamp is needed
--   - encoding: O(·) → an explicit constant C quantified before H, T₂ and X; reason: the standard reading of a uniform O-bound
--   - encoding: the abstract Cha-cha process of Figure 11 with secondary entries (η, q) → ChaChaState without the fragment identifiers q, and the while loop of Access with a budget of H + 1 iterations; reason: no step reads q, so the counts are unchanged; the loop terminates within H iterations, since each iteration strictly increases depth(lca(z, x)) < H
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), Theorem 36, p. 39 (PDF 40), with Theorem 34, p. 34 (PDF 35)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_CursorModel
import Definitions.Def_ChaChaTree_DynOpt_RefTrees
import Definitions.Def_ChaChaTree_DynOpt_ChaChaProcess

set_option autoImplicit false

namespace ChaChaTree.DynOpt

open Real

/-- **Theorem 36, consequence clause** (p. 39). There is a constant `C` such that for every
`n = 2^H ≥ 2` and every full binary tree `T₂` with leaves `0, …, H − 1` (with `B = node T₂ leaf`,
`K = height(B)`, `λ = 1 + log(K + 1)`), some deterministic online BST algorithm on exactly the
keys `[n]`, in the BST model of §5.1, serves every access sequence `X` with total cost
`≤ C·(n + M(X) + Flips₂(X))·λ`, initialization included, where `M` and `Flips₂` are the counts of
the abstract Cha-cha process with reference trees `T₁`, `T₂`. -/
theorem theorem_36 :
    ∃ C : ℝ, ∀ (H : ℕ), 1 ≤ H → ∀ (T₂ : FBT), T₂.numLeaves = H →
      ∃ A : OnlineBSTAlg (2 ^ H), ∀ X : List ℕ, (∀ x ∈ X, x ∈ Finset.Icc 1 (2 ^ H)) →
        A.Serves X ∧
          (A.cost X : ℝ) ≤ C * ((2 ^ H : ℝ) + (exposeCount H T₂ X : ℝ) + (flips2 H T₂ X : ℝ)) *
            (1 + logb 2 (((refB T₂).height : ℝ) + 1)) := by sorry

end ChaChaTree.DynOpt
