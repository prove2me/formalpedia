-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_corollary_35
-- name    : BuchiRabinIndex.LowerBound.corollary_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:57.781214+00:00
-- url     : https://prove2.me/theorems/a5eb9323-be1f-4503-8c90-44b0681a1744
-- title:
--   Corollary 35 — adjacency through the decomposition
-- statement:
--   Let $n\ge2$ and let $x\ne y$ be node names. For either decomposition part $T_i$, if $x,y\in T_i$, then
--   $$x\sim y\text{ in }G_n\quad\Longleftrightarrow\quad \phi_i(x)\sim\phi_i(y)\text{ in }G_{n-1}.$$
--   For $x\in T_1$ and $y\in T_2$,
--   $$x\sim y\text{ in }G_n\quad\Longleftrightarrow\quad \operatorname{weight}(x)+\operatorname{weight}(y)\le n.$$
--
--   These are equivalences in both directions, identifying adjacency within and across the two parts.
--
--   Differences from the source:
--   - encoding: nodes are finite words of positive integers → List Nat with positivity in node and tree predicates; reason: children retain the source’s indices starting at 1
--   - encoding: the unique n-full ordered tree of Definition 12 → the explicitly enumerated positive words of weight at most n−1; reason: this is the same finite tree; no size is fixed
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Corollary 35, p. 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Nodes

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound

/-- STOC 2027 submission #1731, corollary 35; statement only. -/
theorem corollary_35 (n : ℕ) (hn : 2 ≤ n) (x y : Node) (hne : x ≠ y) :
    (x ∈ part1 n → y ∈ part1 n → (Adj n x y ↔ Adj (n - 1) (phi1 x) (phi1 y))) ∧
    (x ∈ part2 n → y ∈ part2 n → (Adj n x y ↔ Adj (n - 1) (phi2 x) (phi2 y))) ∧
    (x ∈ part1 n → y ∈ part2 n → (Adj n x y ↔ weight x + weight y ≤ n)) := by sorry

end BuchiRabinIndex.LowerBound
