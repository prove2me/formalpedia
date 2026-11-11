-- Prove2me | Theorems.Thm_CancelFreeHessian_Formula_virtual_tree
-- name    : CancelFreeHessian.Formula.virtual_tree
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:58:05.046863+00:00
-- url     : https://prove2.me/theorems/b4e9c9f6-54f0-46d2-8266-f5ad321d2584
-- title:
--   §4, Virtual tree — L_i intervals, B_i ⊆ V_i, V_i closed under lowest common ancestors, |V_i| ≤ 2|L_i| − 1, a tree, one V_i-child below each tree child
-- statement:
--   In the tree unfolding of a scalar formula whose output is an operation gate, fix an input $x_i$. Order $L_i$ by depth-first entry time as $\ell_1<\dots<\ell_m$ and let $V_i$ be $L_i$ together with the lowest common ancestors of adjacent pairs $\ell_p,\ell_{p+1}$. Then:
--
--   1. if $w\in B_i$, the leaves of $L_i$ below $w$ form an interval of the order;
--   2. if $w\in B_i$, the last leaf of $L_i$ below the slot-1 child of $w$ and the next one are adjacent and have lowest common ancestor $w$; hence
--   3. $B_i\subseteq V_i$;
--   4. for $p<q$ the lowest common ancestor of $\ell_p,\ell_q$ is the shallowest among those of the adjacent pairs from $p$ to $q$ (it is one of them, and lies above all of them);
--   5. $V_i$ is closed under lowest common ancestors;
--   6. $|V_i|\le 2|L_i|-1$;
--   7. the ancestor relation on $V_i$ is a tree: a nonempty $V_i$ has a node above all of its nodes;
--   8. every node $v\in V_i\setminus L_i$ lies in $B_i$ and has exactly one $V_i$-child below each of its two tree children.
--
--   Differences from the source:
--   - encoding: a DAG of gates with ordered slots 1, 2 → gates numbered 0, …, s − 1 in a topological order (`Dag n`, `WellFormed`), slots as `κ : Fin 2` (κ = 0 is slot 1); reason: every finite DAG has a topological numbering; no instance changes
--   - encoding: the tree unfolding T rooted at the output gate (implicitly an operation gate) → hypothesis `D.IsOp D.out`; reason: if the output is an input or constant gate, T has no node and g is undefined; this only excludes that degenerate case, where no input is active
--   - reading: depth-first entry time (child order unspecified) → entry order with the slot-1 child first (`LeafBefore`); reason: any depth-first order is this one after exchanging the two slots (and the arguments of φ) at some gates, which maps formulas to formulas, so the statement for all formulas covers every DFS
--   - reading: "The ancestor relation on V_i is a tree, found by a stack scan in entry order" → clause 7: a nonempty V_i has a node of V_i above all of its nodes; reason: the ancestor relation on a subset of a tree is a forest, and it is a tree exactly when there is one top node; the stack scan is the algorithm of the goal's bookkeeping, not a separate claim
--   - encoding: |V_i| ≤ 2|L_i| − 1 → `(D.vnodes i).card ≤ 2 * (D.leavesOf i).card - 1` in ℕ; reason: at L_i = ∅ the truncated right side is 0 and V_i = ∅, so the statement is unchanged
-- source:
--   Tianlang Chen, The Cancellation-Free Cost of Hessian Diagonals: Exact Counts, Formulas and Interfaces, STOC 2027 submission (manuscript sha256 de5c3ef4…), p. 12, §4, Virtual tree

import Mathlib
import Definitions.Def_CancelFreeHessian_Formula_Graph
import Definitions.Def_CancelFreeHessian_Formula_Tree

namespace CancelFreeHessian.Formula

/-- **§4, Virtual tree** (Chen, p. 12). For a scalar formula whose output is an operation gate and
an input `x_i`, with `L_i` in depth-first entry order and `V_i` the leaves of `L_i` with the
lowest common ancestors of adjacent pairs:
(1) for `w ∈ B_i` the leaves of `L_i` below `w` form an interval of the order;
(2) for `w ∈ B_i` the last leaf below the slot-1 child and the next one are adjacent with lowest
common ancestor `w`; (3) `B_i ⊆ V_i`;
(4) for `ℓ` before `ℓ'` in `L_i`, their lowest common ancestor is the lowest common ancestor of an
adjacent pair between them and lies above that of every adjacent pair between them;
(5) `V_i` is closed under lowest common ancestors; (6) `|V_i| ≤ 2|L_i| − 1`;
(7) the ancestor relation on `V_i` is a tree: a nonempty `V_i` has a node above all of its nodes;
(8) every node of `V_i ∖ L_i` lies in `B_i` and has exactly one `V_i`-child below each of its two
tree children. -/
theorem virtual_tree (n : ℕ) (D : Dag n) (hD : D.IsScalarFormula) (hout : D.IsOp D.out)
    (i : Fin n) :
    (∀ w ∈ D.branching i, ∀ ℓ₁ ∈ D.leavesOf i, ∀ ℓ₂ ∈ D.leavesOf i, ∀ ℓ₃ ∈ D.leavesOf i,
        D.LeafBefore ℓ₁ ℓ₂ → D.LeafBefore ℓ₂ ℓ₃ →
        D.Below (.leaf ℓ₁) (.gate w) → D.Below (.leaf ℓ₃) (.gate w) →
        D.Below (.leaf ℓ₂) (.gate w)) ∧
      (∀ w ∈ D.branching i, ∃ ℓ ℓ', D.Adjacent i ℓ ℓ' ∧
        D.Below (.leaf ℓ) (D.child w 0) ∧ D.Below (.leaf ℓ') (D.child w 1) ∧
        D.IsLCA (.gate w) (.leaf ℓ) (.leaf ℓ')) ∧
      (∀ w ∈ D.branching i, Node.gate w ∈ D.vnodes i) ∧
      (∀ ℓ ∈ D.leavesOf i, ∀ ℓ' ∈ D.leavesOf i, D.LeafBefore ℓ ℓ' → ∀ w : Node,
        D.IsLCA w (.leaf ℓ) (.leaf ℓ') →
          (∃ m m', D.Adjacent i m m' ∧ (m = ℓ ∨ D.LeafBefore ℓ m) ∧
              (m' = ℓ' ∨ D.LeafBefore m' ℓ') ∧ D.IsLCA w (.leaf m) (.leaf m')) ∧
          ∀ m m' w', D.Adjacent i m m' → (m = ℓ ∨ D.LeafBefore ℓ m) →
            (m' = ℓ' ∨ D.LeafBefore m' ℓ') → D.IsLCA w' (.leaf m) (.leaf m') → D.Below w' w) ∧
      (∀ u ∈ D.vnodes i, ∀ v ∈ D.vnodes i, ∀ w : Node, D.IsLCA w u v → w ∈ D.vnodes i) ∧
      (D.vnodes i).card ≤ 2 * (D.leavesOf i).card - 1 ∧
      ((D.vnodes i).Nonempty → ∃ r ∈ D.vnodes i, ∀ u ∈ D.vnodes i, D.Below u r) ∧
      ∀ v : ℕ, Node.gate v ∈ D.vnodes i →
        v ∈ D.branching i ∧ ∀ κ : Fin 2, ∃! u : Node, D.VChild i v κ u := by sorry

end CancelFreeHessian.Formula
