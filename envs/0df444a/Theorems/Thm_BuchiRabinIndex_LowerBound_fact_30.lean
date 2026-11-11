-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_fact_30
-- name    : BuchiRabinIndex.LowerBound.fact_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:55.329826+00:00
-- url     : https://prove2.me/theorems/d36060b9-1ac9-4f17-94c8-4e274aef0051
-- title:
--   Fact 30 — order facts
-- statement:
--   For positive-index words $x,y$, the relation $y\prec x$ implies $y\prec_{\rm pre}x$, and $x$ is the preorder-last element of $C(x)$. Membership $y\in C(x)$ implies $C(y)\subseteq C(x)$, while mutual membership implies $x=y$.
--
--   Each $C(x)$ is an ordered tree, every ordered tree containing $x$ contains $C(x)$, and $C(x)\cup C(y)$ is an ordered tree. Also,
--   $$x\ne\epsilon\quad\Longrightarrow\quad \{\epsilon,1\}\subseteq C(x).$$
--   Finally, the preorder-last node of any ordered tree is a leaf, and if it is not the root it is the youngest child of its parent.
--
--   All four lettered clauses are included; the root has no parent, so only the parent clause is conditional at the singleton tree.
--
--   Differences from the source:
--   - encoding: nodes are finite words of positive integers → List Nat with positivity in node and tree predicates; reason: children retain the source’s indices starting at 1
--   - encoding: the last node is the youngest child of its parent → the parent clause is conditional on the last node not being the root; reason: the root of the singleton tree has no parent
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Fact 30, p. 25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Nodes

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound

/-- STOC 2027 submission #1731, fact 30; statement only. -/
theorem fact_30 (x y : Node) (hx : Positive x) (hy : Positive y) :
    (Prec y x → PreLt y x) ∧ Last (chain x) x ∧
    (y ∈ chain x → chain y ⊆ chain x) ∧
    (x ∈ chain y → y ∈ chain x → x = y) ∧
    Ordered (chain x) ∧
    (∀ T, Ordered T → x ∈ T → chain x ⊆ T) ∧
    Ordered (chain x ∪ chain y) ∧
    (x ≠ [] → ({[], [1]} : Finset Node) ⊆ chain x) ∧
    (∀ T z, Ordered T → Last T z → Leaf T z ∧ (z ≠ [] → Youngest T z)) := by sorry

end BuchiRabinIndex.LowerBound
