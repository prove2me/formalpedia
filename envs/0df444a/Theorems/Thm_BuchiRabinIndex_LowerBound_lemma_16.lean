-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_16
-- name    : BuchiRabinIndex.LowerBound.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:32:00.954691+00:00
-- url     : https://prove2.me/theorems/9f8b1511-5e22-42d0-9824-30fae294bacc
-- title:
--   Lemma 16 — decomposition
-- statement:
--   For $n\ge2$, let $T_1=\{1\sigma:\sigma\in T^{(n-1)}\}$ and let $T_2$ be obtained by incrementing the first entry of each nonroot word of $T^{(n-1)}$. Then
--   $$T^{(n)}=\{\epsilon\}\cup T_1\cup T_2.$$
--   The maps $\phi_1(1\sigma)=\sigma$ and $\phi_2((s+1)\sigma)=s\sigma$ are bijections onto $T^{(n-1)}$ and $T^{(n-1)}\setminus\{\epsilon\}$, respectively. For each node in either part,
--   $$\operatorname{weight}(x)=\operatorname{weight}(\phi_i(x))+1.$$
--
--   Both bijections and both weight identities are included. This decomposition relates successive coexistence graphs.
--
--   Differences from the source:
--   - encoding: nodes are finite words of positive integers → List Nat with positivity in node and tree predicates; reason: children retain the source’s indices starting at 1
--   - encoding: the unique n-full ordered tree of Definition 12 → the explicitly enumerated positive words of weight at most n−1; reason: this is the same finite tree; no size is fixed
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Lemma 16, p. 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Nodes

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound

/-- STOC 2027 submission #1731, lemma 16; statement only. -/
theorem lemma_16 (n : ℕ) (hn : 2 ≤ n) :
    fullTree n = {[]} ∪ part1 n ∪ part2 n ∧
    Set.BijOn phi1 {x | x ∈ part1 n} {x | x ∈ fullTree (n - 1)} ∧
    Set.BijOn phi2 {x | x ∈ part2 n} {x | x ∈ (fullTree (n - 1)).erase []} ∧
    (∀ x ∈ part1 n, weight x = weight (phi1 x) + 1) ∧
    (∀ x ∈ part2 n, weight x = weight (phi2 x) + 1) := by sorry

end BuchiRabinIndex.LowerBound
