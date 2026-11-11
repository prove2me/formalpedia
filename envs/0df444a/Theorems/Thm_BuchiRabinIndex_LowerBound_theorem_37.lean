-- Prove2me | Theorems.Thm_BuchiRabinIndex_LowerBound_theorem_37
-- name    : BuchiRabinIndex.LowerBound.theorem_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:57.351257+00:00
-- url     : https://prove2.me/theorems/8bd8d960-4ee3-4865-9e85-ced23deb690d
-- title:
--   Theorem 37 — clique number
-- statement:
--   The coexistence graph has clique number
--   $$\omega(G_1)=1,\qquad \omega(G_n)=\begin{cases}2^{n/2}&n\ge2\text{ even},\\3\cdot2^{(n-3)/2}&n\ge3\text{ odd}.\end{cases}$$
--   Moreover, for every $n\ge1$ and $\lfloor n/2\rfloor<c\le n-1$,
--   $$g(n,c)=\omega(G_n).$$
--
--   The final clause retains the domain of $g$ from Definition 34. Exponents are integers under the indicated parity conditions. This supplies the explicit values appearing again in the goal.
--
--   Differences from the source:
--   - encoding: nodes are finite words of positive integers → List Nat with positivity in node and tree predicates; reason: children retain the source’s indices starting at 1
--   - encoding: the unique n-full ordered tree of Definition 12 → the explicitly enumerated positive words of weight at most n−1; reason: this is the same finite tree; no size is fixed
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Theorem 37, p. 27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Nodes

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound

/-- STOC 2027 submission #1731, theorem 37; statement only. -/
theorem theorem_37  :
    omega 1 = 1 ∧
    (∀ n, 2 ≤ n →
      (Even n → omega n = 2 ^ (n / 2)) ∧
      (Odd n → omega n = 3 * 2 ^ ((n - 3) / 2))) ∧
    (∀ n c, 1 ≤ n → n / 2 < c → c ≤ n - 1 → g n c = omega n) := by sorry

end BuchiRabinIndex.LowerBound
